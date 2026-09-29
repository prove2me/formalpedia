-- Prove2me | solution 1 for mme_flatteningRank_MMObj_bc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-06-05T03:28:15.278682+00:00
-- url     : https://prove2.me/submissions/979f4a10-b372-4d29-9fe6-8e638e10ee88

import Mathlib.LinearAlgebra.PiTensorProduct.Basic
import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Logic.Equiv.Fin.Basic
import Definitions.Def_mme_omega
import Definitions.Def_mme_tensor
import Definitions.Def_mme_tensor_rank
import Definitions.Def_mme_flattening

namespace MME

/-- The singleton split `S = {1}` of `Fin 3`. -/
noncomputable def split1_sol : Split (Fin 3) where
  S := {(1 : Fin 3)}
  hS := Finset.singleton_nonempty _
  hSc := by
    refine Finset.nonempty_iff_ne_empty.mpr ?_
    intro h
    have hcard : ({(1 : Fin 3)}ᶜ : Finset (Fin 3)).card = 0 := by rw [h]; rfl
    rw [Finset.card_compl, Finset.card_singleton, Fintype.card_fin] at hcard
    omega

end MME

open MME



/-!
# `b*c ≤ flatteningRank σ_1 (MMObj K a b c)` for `a ≥ 1`

Mode-1 cyclic analogue of `Sol_mme_flatteningRank_MMObj_ab`. We construct `b*c` linearly
independent vectors in the range of the mode-1 flattening map.

For each (j₀, k₀) ∈ Fin b × Fin c, take the left-block basis dual at `(j₀, k₀)`. Its
image under the flattening map equals `∑_i R_{i,j₀,k₀}`, where R is the right-block
pure tensor with mode-0 entry `e_{(i,j₀)}` and mode-2 entry `e_{(k₀,i)}`. These images
for different (j₀, k₀) have disjoint basis support, so they're linearly independent
when a ≥ 1. -/

set_option maxHeartbeats 1600000

universe u

open PiTensorProduct TensorProduct BigOperators Module

namespace MMEFlatteningRankMMObjBcSol

open MME

variable {K : Type u} [Field K]

section MMObj_bc

/-- Alias for `split1_sol`. -/
private noncomputable abbrev σ1 : Split (Fin 3) := split1_sol

/-- `σ1.S = {1}` has a unique element. -/
private instance σ1_S_subsingleton : Subsingleton (σ1 : Split (Fin 3)).S := by
  refine ⟨fun x y => ?_⟩
  ext
  have hx : (x : Fin 3) ∈ ({(1 : Fin 3)} : Finset (Fin 3)) := x.2
  have hy : (y : Fin 3) ∈ ({(1 : Fin 3)} : Finset (Fin 3)) := y.2
  rw [Finset.mem_singleton] at hx hy
  rw [hx, hy]

/-- The element `1 : Fin 3` packaged as a member of `σ1.S = {1}`. -/
private def sOneL : (σ1 : Split (Fin 3)).S :=
  ⟨(1 : Fin 3), by simp [σ1, split1_sol]⟩

/-- `σ1.S` is nonempty. -/
private instance σ1_S_nonempty : Nonempty (σ1 : Split (Fin 3)).S := ⟨sOneL⟩

/-- Decidable equality on `σ1.S`. -/
private instance σ1_S_decEq : DecidableEq (σ1 : Split (Fin 3)).S := by
  intro x y
  exact Decidable.isTrue (Subsingleton.elim _ _)

/-- The element `1 : Fin 3` is in `σ1.S`. -/
private lemma sOneL_val : (sOneL : (σ1 : Split (Fin 3)).S).val = 1 := rfl

/-- For any `s ∈ Sc σ1`, `s.val ≠ 1`. -/
private lemma sc_ne_one (s : Sc (σ1 : Split (Fin 3))) : (s.val : Fin 3) ≠ 1 := by
  intro h
  have hm : (s.val : Fin 3) ∈ (σ1 : Split (Fin 3)).Sᶜ := s.2
  rw [h] at hm
  have h1 : (1 : Fin 3) ∈ (σ1 : Split (Fin 3)).S := by
    show (1 : Fin 3) ∈ ({(1 : Fin 3)} : Finset (Fin 3))
    rw [Finset.mem_singleton]
  exact Finset.mem_compl.mp hm h1

/-- The basis-index type for each mode of `MMObj K a b c`, uniformly on `Fin 3`. -/
private def MMIdx (a b c : ℕ) : Fin 3 → Type
  | ⟨0, _⟩ => Fin a × Fin b
  | ⟨1, _⟩ => Fin b × Fin c
  | ⟨2, _⟩ => Fin c × Fin a
  | ⟨_+3, h⟩ => absurd h (by omega)

private instance MMIdx_fintype (a b c : ℕ) (i : Fin 3) : Fintype (MMIdx a b c i) := by
  match i with
  | ⟨0, _⟩ => exact inferInstanceAs (Fintype (Fin a × Fin b))
  | ⟨1, _⟩ => exact inferInstanceAs (Fintype (Fin b × Fin c))
  | ⟨2, _⟩ => exact inferInstanceAs (Fintype (Fin c × Fin a))

private instance MMIdx_decEq (a b c : ℕ) (i : Fin 3) : DecidableEq (MMIdx a b c i) := by
  match i with
  | ⟨0, _⟩ => exact inferInstanceAs (DecidableEq (Fin a × Fin b))
  | ⟨1, _⟩ => exact inferInstanceAs (DecidableEq (Fin b × Fin c))
  | ⟨2, _⟩ => exact inferInstanceAs (DecidableEq (Fin c × Fin a))

/-- Per-mode basis (matching `MMSpace`). -/
private noncomputable def MMBasis (K : Type u) [Field K] (a b c : ℕ) :
    ∀ i : Fin 3, Basis (MMIdx a b c i) K (MMSpace K a b c i) := by
  intro i
  match i with
  | ⟨0, _⟩ => exact Pi.basisFun K (Fin a × Fin b)
  | ⟨1, _⟩ => exact Pi.basisFun K (Fin b × Fin c)
  | ⟨2, _⟩ => exact Pi.basisFun K (Fin c × Fin a)

/-- Left-block basis: indexed by `σ1.S → Fin b × Fin c`. -/
private noncomputable def bL (a b c : ℕ) :
    Basis ((σ1 : Split (Fin 3)).S → Fin b × Fin c) K
      (PiTensorProduct K (fun i : (σ1 : Split (Fin 3)).S =>
        (MMObj K a b c).V i.val)) :=
  Basis.piTensorProduct (fun i : (σ1 : Split (Fin 3)).S =>
    (show (MMIdx a b c i.val) = (Fin b × Fin c) by
      have hx1 : (i : Fin 3) = 1 := Finset.mem_singleton.mp i.2
      rw [hx1]; rfl) ▸ MMBasis K a b c i.val)

/-- Right-block basis: indexed by `∀ s : Sc σ1, MMIdx a b c s.val`. -/
private noncomputable def bR (a b c : ℕ) :
    Basis (∀ s : Sc (σ1 : Split (Fin 3)), MMIdx a b c s.val) K
      (PiTensorProduct K (fun i : Sc (σ1 : Split (Fin 3)) =>
        (MMObj K a b c).V i.val)) :=
  Basis.piTensorProduct (fun s : Sc (σ1 : Split (Fin 3)) => MMBasis K a b c s.val)

/-- The right-block basis index `g_{j₀,k₀,i}` corresponding to the pure tensor with
mode-0 entry `e_{(i,j₀)}` and mode-2 entry `e_{(k₀,i)}`. -/
private noncomputable def gR (a b c : ℕ)
    (j₀ : Fin b) (k₀ : Fin c) (i : Fin a) :
    ∀ s : Sc (σ1 : Split (Fin 3)), MMIdx a b c s.val := fun s =>
  match h : (s.val : Fin 3) with
  | ⟨0, _⟩ => (i, j₀)
  | ⟨1, _⟩ => absurd h (sc_ne_one s)
  | ⟨2, _⟩ => (k₀, i)

/-- The candidate vector `vec (j₀, k₀)` in `V_right`: sum of right-block basis tensors
indexed by `gR j₀ k₀ i` for `i ∈ Fin a`. -/
private noncomputable def vec (a b c : ℕ) (jk : Fin b × Fin c) :
    PiTensorProduct K (fun i : Sc (σ1 : Split (Fin 3)) => (MMObj K a b c).V i.val) :=
  ∑ i : Fin a, bR a b c (gR a b c jk.1 jk.2 i)

/-- A concrete element of `Sc σ1` with value `0`. -/
private noncomputable def sZeroC : Sc (σ1 : Split (Fin 3)) :=
  ⟨(0 : Fin 3), by
    show (0 : Fin 3) ∈ (σ1 : Split (Fin 3)).Sᶜ
    rw [Finset.mem_compl]
    intro h
    have : (0 : Fin 3) ∈ ({(1 : Fin 3)} : Finset (Fin 3)) := h
    have h10 : (0 : Fin 3) = 1 := Finset.mem_singleton.mp this
    exact absurd h10 (by decide)⟩

/-- A concrete element of `Sc σ1` with value `2`. -/
private noncomputable def sTwoC : Sc (σ1 : Split (Fin 3)) :=
  ⟨(2 : Fin 3), by
    show (2 : Fin 3) ∈ (σ1 : Split (Fin 3)).Sᶜ
    rw [Finset.mem_compl]
    intro h
    have : (2 : Fin 3) ∈ ({(1 : Fin 3)} : Finset (Fin 3)) := h
    have h12 : (2 : Fin 3) = 1 := Finset.mem_singleton.mp this
    exact absurd h12 (by decide)⟩

private lemma sZeroC_val : (sZeroC : Sc (σ1 : Split (Fin 3))).val = (0 : Fin 3) := rfl
private lemma sTwoC_val : (sTwoC : Sc (σ1 : Split (Fin 3))).val = (2 : Fin 3) := rfl

/-- `gR j₀ k₀ i` evaluated at `sZeroC` (mode-0 slot) gives `(i, j₀)`. -/
private lemma gR_at_sZeroC (a b c : ℕ) (j₀ : Fin b) (k₀ : Fin c) (i : Fin a) :
    (gR a b c j₀ k₀ i sZeroC : MMIdx a b c (sZeroC : Sc (σ1 : Split (Fin 3))).val) = (i, j₀) := by
  unfold gR
  rfl

/-- `gR j₀ k₀ i` evaluated at `sTwoC` (mode-2 slot) gives `(k₀, i)`. -/
private lemma gR_at_sTwoC (a b c : ℕ) (j₀ : Fin b) (k₀ : Fin c) (i : Fin a) :
    (gR a b c j₀ k₀ i sTwoC : MMIdx a b c (sTwoC : Sc (σ1 : Split (Fin 3))).val) = (k₀, i) := by
  unfold gR
  rfl

/-- The combined index `(jk, i) ↦ gR jk.1 jk.2 i` is injective. -/
private lemma gR_injective (a b c : ℕ) :
    Function.Injective (fun (p : (Fin b × Fin c) × Fin a) =>
      gR a b c p.1.1 p.1.2 p.2) := by
  rintro ⟨⟨j₀, k₀⟩, i⟩ ⟨⟨j₀', k₀'⟩, i'⟩ h
  simp only at h
  -- evaluate at sZeroC to get (i, j₀) = (i', j₀')
  have h1 : gR a b c j₀ k₀ i sZeroC = gR a b c j₀' k₀' i' sZeroC := by
    rw [h]
  rw [gR_at_sZeroC, gR_at_sZeroC] at h1
  -- evaluate at sTwoC to get (k₀, i) = (k₀', i')
  have h2 : gR a b c j₀ k₀ i sTwoC = gR a b c j₀' k₀' i' sTwoC := by
    rw [h]
  rw [gR_at_sTwoC, gR_at_sTwoC] at h2
  obtain ⟨hi, hj⟩ := Prod.mk.inj h1
  obtain ⟨hk, _⟩ := Prod.mk.inj h2
  simp [hi, hj, hk]

/-- For different `jk ≠ jk'`, the images `{gR jk.1 jk.2 i | i}` and
`{gR jk'.1 jk'.2 i | i}` are disjoint. -/
private lemma gR_disjoint (a b c : ℕ) {jk jk' : Fin b × Fin c} (hne : jk ≠ jk')
    (i i' : Fin a) :
    gR a b c jk.1 jk.2 i ≠ gR a b c jk'.1 jk'.2 i' := by
  intro h
  apply hne
  -- evaluate at sZeroC for j-component
  have h1 : gR a b c jk.1 jk.2 i sZeroC = gR a b c jk'.1 jk'.2 i' sZeroC := by rw [h]
  rw [gR_at_sZeroC, gR_at_sZeroC] at h1
  obtain ⟨_, hj⟩ := Prod.mk.inj h1
  -- evaluate at sTwoC for k-component
  have h2 : gR a b c jk.1 jk.2 i sTwoC = gR a b c jk'.1 jk'.2 i' sTwoC := by rw [h]
  rw [gR_at_sTwoC, gR_at_sTwoC] at h2
  obtain ⟨hk, _⟩ := Prod.mk.inj h2
  exact Prod.ext hj hk

/-- **Linear independence of `vec`.** Uses dual functionals:
the basis coord `bR.coord (gR jk.1 jk.2 ⟨0, ha⟩)` evaluates to 1 on `vec jk` and to 0
on `vec jk'` for `jk ≠ jk'`. -/
private lemma vec_linearIndependent (a b c : ℕ) (ha : 1 ≤ a) :
    LinearIndependent K (vec (K := K) a b c) := by
  -- the dual functional family
  let φ : Fin b × Fin c → Dual K
      (PiTensorProduct K (fun i : Sc (σ1 : Split (Fin 3)) =>
        (MMObj K a b c).V i.val)) :=
    fun jk => (bR a b c).coord (gR a b c jk.1 jk.2 ⟨0, ha⟩)
  refine LinearIndependent.of_pairwise_dual_eq_zero_one (v := vec a b c) (f := φ) ?_ ?_
  · intro jk jk' hne
    show φ jk (vec a b c jk') = 0
    unfold vec
    rw [map_sum]
    apply Finset.sum_eq_zero
    intro i _
    rw [Basis.coord_apply, Basis.repr_self_apply]
    rw [if_neg]
    intro h
    exact gR_disjoint a b c (Ne.symm hne) i ⟨0, ha⟩ h
  · intro jk
    show φ jk (vec a b c jk) = 1
    unfold vec
    rw [map_sum]
    rw [Finset.sum_eq_single (⟨0, ha⟩ : Fin a)]
    · rw [Basis.coord_apply, Basis.repr_self_apply, if_pos rfl]
    · intro i _ hi
      rw [Basis.coord_apply, Basis.repr_self_apply, if_neg]
      intro h
      have hinj := gR_injective a b c
      have : ((jk, i) : (Fin b × Fin c) × Fin a) = ((jk, ⟨0, ha⟩) : (Fin b × Fin c) × Fin a) := by
        apply hinj
        exact h
      have := (Prod.mk.inj this).2
      exact hi this
    · intro h; exact absurd (Finset.mem_univ _) h

/-! ### Step 2: Each `vec jk` is in the range of the flattening map. -/

/-- The dual functional that "picks out coordinate `jk`" via the singleton
identification of the left block. Concretely: pull back the evaluation-at-`jk`
functional on `Fin b × Fin c → K` through `subsingletonEquiv sOneL`. -/
private noncomputable def dualL (a b c : ℕ) (jk : Fin b × Fin c) :
    Dual K (PiTensorProduct K (fun i : (σ1 : Split (Fin 3)).S =>
      (MMObj K a b c).V i.val)) :=
  (LinearMap.proj jk : (Fin b × Fin c → K) →ₗ[K] K).comp
    ((PiTensorProduct.subsingletonEquiv sOneL).toLinearMap :
      PiTensorProduct K (fun i : (σ1 : Split (Fin 3)).S =>
        (MMObj K a b c).V i.val) →ₗ[K] (Fin b × Fin c → K))

/-- `dualL jk` applied to a pure tensor `tprod K v` evaluates `v sOneL` at `jk`. -/
private lemma dualL_tprod (a b c : ℕ) (jk : Fin b × Fin c)
    (v : ∀ s : (σ1 : Split (Fin 3)).S, (MMObj K a b c).V s.val) :
    dualL a b c jk (tprod K v) = (v sOneL : Fin b × Fin c → K) jk := by
  unfold dualL
  have h : (PiTensorProduct.subsingletonEquiv sOneL : PiTensorProduct K
      (fun i : (σ1 : Split (Fin 3)).S => (MMObj K a b c).V i.val) ≃ₗ[K]
      (MMObj K a b c).V (sOneL : (σ1 : Split (Fin 3)).S).val) (tprod K v) =
      v sOneL :=
    PiTensorProduct.subsingletonEquiv_apply_tprod _ _
  show (PiTensorProduct.subsingletonEquiv sOneL) (tprod K v) jk = v sOneL jk
  rw [h]

/-- The mode-wise data function for the (i, j, k) term of `MMTensor K a b c`. -/
private noncomputable def modeData (a b c : ℕ) (i : Fin a) (j : Fin b) (k : Fin c) :
    ∀ s : Fin 3, MMSpace K a b c s := fun s =>
  match s with
  | ⟨0, _⟩ => (Pi.single (i, j) 1 : Fin a × Fin b → K)
  | ⟨1, _⟩ => (Pi.single (j, k) 1 : Fin b × Fin c → K)
  | ⟨2, _⟩ => (Pi.single (k, i) 1 : Fin c × Fin a → K)

/-- `MMTensor K a b c` written as a triple sum using `modeData`. -/
private lemma MMTensor_eq_sum (a b c : ℕ) :
    MMTensor K a b c = ∑ i : Fin a, ∑ j : Fin b, ∑ k : Fin c,
      tprod K (modeData (K := K) a b c i j k) := by
  rfl

/-- The "left" tensor of the (i, j, k) term after `splitTensorEquiv σ1`. -/
private noncomputable def Lterm (a b c : ℕ) (i : Fin a) (j : Fin b) (k : Fin c) :
    PiTensorProduct K (fun s : (σ1 : Split (Fin 3)).S => (MMObj K a b c).V s.val) :=
  tprod K (fun s : (σ1 : Split (Fin 3)).S => modeData a b c i j k s.val)

/-- The "right" tensor of the (i, j, k) term after `splitTensorEquiv σ1`. -/
private noncomputable def Rterm (a b c : ℕ) (i : Fin a) (j : Fin b) (k : Fin c) :
    PiTensorProduct K (fun s : Sc (σ1 : Split (Fin 3)) => (MMObj K a b c).V s.val) :=
  tprod K (fun s : Sc (σ1 : Split (Fin 3)) => modeData a b c i j k s.val)

/-- `splitTensorEquiv` of one pure term decomposes into `Lterm ⊗ₜ Rterm`. -/
private lemma splitTensorEquiv_term (a b c : ℕ) (i : Fin a) (j : Fin b) (k : Fin c) :
    splitTensorEquiv σ1 (tprod K (modeData (K := K) a b c i j k))
      = Lterm a b c i j k ⊗ₜ[K] Rterm a b c i j k :=
  splitTensorEquiv_tprod _ _

/-- The `dualL jk` value on `Lterm i j k` is `δ_{(j,k) = jk}`. -/
private lemma dualL_Lterm (a b c : ℕ) (jk : Fin b × Fin c)
    (i : Fin a) (j : Fin b) (k : Fin c) :
    dualL a b c jk (Lterm a b c i j k) = if (j, k) = jk then (1 : K) else 0 := by
  unfold Lterm
  refine (dualL_tprod a b c jk _).trans ?_
  show (modeData (K := K) a b c i j k (sOneL : (σ1 : Split (Fin 3)).S).val :
    Fin b × Fin c → K) jk = if (j, k) = jk then (1 : K) else 0
  rw [show modeData (K := K) a b c i j k (sOneL : (σ1 : Split (Fin 3)).S).val =
      (Pi.single (j, k) 1 : Fin b × Fin c → K) from rfl]
  rw [Pi.single_apply]
  by_cases h : jk = (j, k)
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (Ne.symm h)]

/-- `Rterm i j k = bR (gR j k i)`. -/
private lemma Rterm_eq_bR (a b c : ℕ) (i : Fin a) (j : Fin b) (k : Fin c) :
    (Rterm (K := K) a b c i j k) = bR (K := K) a b c (gR a b c j k i) := by
  unfold Rterm bR
  refine Eq.trans ?_ (Basis.piTensorProduct_apply _ _).symm
  congr 1
  funext s
  show modeData (K := K) a b c i j k s.val = MMBasis K a b c s.val (gR a b c j k i s)
  rcases s with ⟨sv, hsv⟩
  have hne : sv ≠ 1 := sc_ne_one ⟨sv, hsv⟩
  match sv, hne with
  | ⟨0, hsv0⟩, _ =>
    show (Pi.single (i, j) 1 : Fin a × Fin b → K) =
      MMBasis K a b c (⟨0, hsv0⟩ : Fin 3) (gR a b c j k i ⟨⟨0, hsv0⟩, hsv⟩)
    show (Pi.single (i, j) 1 : Fin a × Fin b → K) =
      Pi.basisFun K (Fin a × Fin b) (gR a b c j k i ⟨⟨0, hsv0⟩, hsv⟩)
    exact (Pi.basisFun_apply ..).symm
  | ⟨2, hsv2⟩, _ =>
    show (Pi.single (k, i) 1 : Fin c × Fin a → K) =
      MMBasis K a b c (⟨2, hsv2⟩ : Fin 3) (gR a b c j k i ⟨⟨2, hsv2⟩, hsv⟩)
    show (Pi.single (k, i) 1 : Fin c × Fin a → K) =
      Pi.basisFun K (Fin c × Fin a) (gR a b c j k i ⟨⟨2, hsv2⟩, hsv⟩)
    exact (Pi.basisFun_apply ..).symm
  | ⟨1, _⟩, h => exact absurd rfl h

/-- The key formula expressing `flatteningMap σ1 (MMObj K a b c) (dualL jk)` as
`∑_{i,j,k} δ_{(j,k)=jk} • bR (gR j k i) = vec jk`. -/
private lemma flatteningMap_MMObj_dualL_eq_vec (a b c : ℕ) (jk : Fin b × Fin c) :
    flatteningMap σ1 (MMObj K a b c) (dualL a b c jk) = vec a b c jk := by
  unfold flatteningMap
  show tensorToDualHom K _ _ (splitTensorEquiv σ1 (MMTensor K a b c)) (dualL a b c jk) =
    vec a b c jk
  rw [MMTensor_eq_sum]
  rw [show splitTensorEquiv σ1 (∑ i : Fin a, ∑ j : Fin b, ∑ k : Fin c,
        tprod K (modeData (K := K) a b c i j k))
      = ∑ i : Fin a, ∑ j : Fin b, ∑ k : Fin c,
        Lterm a b c i j k ⊗ₜ[K] Rterm a b c i j k from ?_]
  swap
  · simp only [map_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    refine Finset.sum_congr rfl (fun j _ => ?_)
    refine Finset.sum_congr rfl (fun k _ => ?_)
    exact splitTensorEquiv_term a b c i j k
  have hreduce : ((tensorToDualHom K
      (PiTensorProduct K (fun s : (σ1 : Split (Fin 3)).S => (MMObj K a b c).V s.val))
      (PiTensorProduct K (fun s : Sc (σ1 : Split (Fin 3)) => (MMObj K a b c).V s.val)))
      (∑ i : Fin a, ∑ j : Fin b, ∑ k : Fin c,
        Lterm a b c i j k ⊗ₜ[K] Rterm a b c i j k)) (dualL a b c jk) =
      ∑ i : Fin a, ∑ j : Fin b, ∑ k : Fin c,
        dualL (K := K) a b c jk (Lterm a b c i j k) • Rterm (K := K) a b c i j k := by
    rw [map_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [map_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [map_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [tensorToDualHom_tmul]
  change ((tensorToDualHom K
      (PiTensorProduct K (fun s : (σ1 : Split (Fin 3)).S => (MMObj K a b c).V s.val))
      (PiTensorProduct K (fun s : Sc (σ1 : Split (Fin 3)) => (MMObj K a b c).V s.val)))
      (∑ i : Fin a, ∑ j : Fin b, ∑ k : Fin c,
        Lterm a b c i j k ⊗ₜ[K] Rterm a b c i j k)) (dualL a b c jk) = _
  rw [hreduce]
  simp_rw [dualL_Lterm]
  simp_rw [Rterm_eq_bR]
  -- Goal:
  -- ∑ i, ∑ j, ∑ k, (if (j,k) = jk then 1 else 0) • bR (gR j k i) = vec jk
  -- vec jk = ∑_i bR (gR jk.1 jk.2 i).
  -- For fixed i, the inner ∑_{j,k} selects (j,k) = jk.
  -- Strategy: collapse j, k for each i.
  unfold vec
  -- Goal: ∑ i, ∑ j, ∑ k, (if (j,k) = jk then 1 else 0) • bR (gR j k i) =
  --       ∑ i, bR (gR jk.1 jk.2 i)
  refine Finset.sum_congr rfl (fun i _ => ?_)
  -- For each i, collapse the (j, k) double sum.
  rw [Finset.sum_eq_single jk.1]
  · rw [Finset.sum_eq_single jk.2]
    · rw [if_pos rfl, one_smul]
    · intro k _ hk
      rw [if_neg, zero_smul]
      intro h
      apply hk
      exact (Prod.mk.inj h).2
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro j _ hj
    rw [Finset.sum_eq_zero]
    intro k _
    rw [if_neg, zero_smul]
    intro h
    apply hj
    exact (Prod.mk.inj h).1
  · intro h; exact absurd (Finset.mem_univ _) h

/-- **`vec jk ∈ range (flatteningMap σ1 (MMObj K a b c))`.** -/
private lemma vec_mem_range (a b c : ℕ) (jk : Fin b × Fin c) :
    vec a b c jk ∈ LinearMap.range (flatteningMap σ1 (MMObj K a b c)) := by
  exact ⟨dualL a b c jk, flatteningMap_MMObj_dualL_eq_vec a b c jk⟩

end MMObj_bc

end MMEFlatteningRankMMObjBcSol

/-! ### Main result (top-level for platform upload) -/

open MMEFlatteningRankMMObjBcSol MME

/-- The mode-1 flattening rank of `MMObj K a b c` is at least `b * c` when `a ≥ 1`.

Proof: we construct `b * c` linearly independent vectors `vec jk` for `jk ∈ Fin b × Fin c`
in the range of the flattening map. Each `vec jk = ∑_i bR (gR jk.1 jk.2 i)` is a sum of
right-block basis tensors, and the index map `(jk, i) ↦ gR jk.1 jk.2 i` is injective;
combined with `a ≥ 1`, this yields linear independence. -/
theorem solution {K : Type u} [Field K] (a b c : ℕ) (ha : 1 ≤ a) :
    b * c ≤ MME.flatteningRank MME.split1_sol (MME.MMObj K a b c) := by
  unfold flatteningRank
  set V_right := PiTensorProduct K (fun i : Sc (σ1 : Split (Fin 3)) =>
    (MMObj K a b c).V i.val) with hVright
  have : FiniteDimensional K V_right :=
    Module.Finite.of_basis (bR a b c)
  set rangeFM := LinearMap.range (flatteningMap σ1 (MMObj K a b c)) with hrangeFM
  let vecInRange : Fin b × Fin c → rangeFM := fun jk =>
    ⟨vec a b c jk, vec_mem_range a b c jk⟩
  have hLI : LinearIndependent K vecInRange := by
    have hLI₀ : LinearIndependent K (vec (K := K) a b c) :=
      vec_linearIndependent a b c ha
    exact hLI₀.of_comp rangeFM.subtype
  have hcard : Fintype.card (Fin b × Fin c) = b * c := by
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
  have := hLI.fintype_card_le_finrank (R := K) (M := rangeFM)
  rw [hcard] at this
  exact this
