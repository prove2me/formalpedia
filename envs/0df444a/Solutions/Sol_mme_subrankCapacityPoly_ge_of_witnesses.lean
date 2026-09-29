-- Prove2me | solution 1 for mme_subrankCapacityPoly_ge_of_witnesses
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-06-07T14:40:31.909082+00:00
-- url     : https://prove2.me/submissions/1490c2d1-0110-4cf5-8d58-7e0ac93e1d1a

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Topology.Order.Basic
import Definitions.Def_mme_subrank_capacity_poly
import Definitions.Def_mme_tensor_rank
import Definitions.Def_mme_flattening
import Theorems.Thm_mme_flatteningRank_MMObj_ab
import Theorems.Thm_mme_flatteningRank_MMObj_bc
import Theorems.Thm_mme_flatteningRank_MMObj_ca

open MME BigOperators Filter



/-!
# `V ≤ subrankCapacityPoly T` from polynomial witnesses

The polynomial-witness construction satisfied by `V` (with `1 ≤ V`) directly
puts `V` into the defining set `S` of `subrankCapacityPoly T = sSup S`. The
content of this file is to show `S` is bounded above so `Real.sSup` is
well-defined and `le_csSup` applies.

## BddAbove witness

For any `V' ∈ S` with witnesses `(N, k, aᵢ, bᵢ, cᵢ)`:

- For each `i` with `aᵢbᵢcᵢ ≥ 1`, all three are ≥ 1, and the three cyclic
  flattening-rank bounds give `aᵢbᵢ ≤ D_0^N`, `bᵢcᵢ ≤ D_1^N`, `cᵢaᵢ ≤ D_2^N`,
  where `D_j = ∏_{i ∈ Sᶜ_j} finrank (T.V i)`.
- Multiplying: `(aᵢbᵢcᵢ)^2 ≤ (D_0 D_1 D_2)^N = D^{2N}` where
  `D := (finrank V_0)(finrank V_1)(finrank V_2)`.
- So `aᵢbᵢcᵢ ≤ D^N`, hence `(aᵢbᵢcᵢ)^{1/3} ≤ D^{N/3}`.
- Summing: `∑ᵢ (aᵢbᵢcᵢ)^{1/3} ≤ k · D^{N/3} ≤ (N+1)^c · D^{N/3}`.
- So `V'^N (1-ε) ≤ (N+1)^c · D^{N/3}`. Taking log and using ∃ᶠ N → ∞ gives
  `V' ≤ D^{1/3}`. -/

open MME BigOperators Filter Topology
open PiTensorProduct TensorProduct Module

universe u

set_option maxHeartbeats 1600000

namespace MMESubrankPolyGe

variable {K : Type u} [Field K]

/-! ## Local Restrict preorder helpers. -/

private theorem restrict_refl {d : ℕ} (X : TensorObj K d) :
    TensorObj.Restrict X X :=
  ⟨fun _ => LinearMap.id, by rw [PiTensorProduct.map_id]; rfl⟩

private theorem restrict_trans {d : ℕ} {X Y Z : TensorObj K d}
    (hXY : TensorObj.Restrict X Y) (hYZ : TensorObj.Restrict Y Z) :
    TensorObj.Restrict X Z := by
  obtain ⟨f, hf⟩ := hXY
  obtain ⟨g, hg⟩ := hYZ
  refine ⟨fun i => f i ∘ₗ g i, ?_⟩
  rw [PiTensorProduct.map_comp, LinearMap.comp_apply, hg, hf]

/-! ## (1) Per-block restriction inside `bigAdd` -/

private theorem map_zero_pitensor {d : ℕ} {V W : Fin d → Type u}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)] (hd : 0 < d)
    (t : PiTensorProduct K V) :
    PiTensorProduct.map (fun i => (0 : V i →ₗ[K] W i)) t = 0 := by
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  induction t using PiTensorProduct.induction_on with
  | smul_tprod r v =>
    rw [map_smul, PiTensorProduct.map_tprod]
    have h0 : (tprod K (fun i => (0 : V i →ₗ[K] W i) (v i)) : PiTensorProduct K W) = 0 := by
      refine MultilinearMap.map_coord_zero (tprod K) (Classical.arbitrary (Fin d)) ?_
      simp
    rw [h0]; simp
  | add x y ihx ihy => rw [map_add, ihx, ihy, zero_add]

private theorem restrict_add_left {d : ℕ} (hd : 0 < d) (X Y : TensorObj K d) :
    TensorObj.Restrict X (TensorObj.add X Y) := by
  refine ⟨fun i => LinearMap.fst K (X.V i) (Y.V i), ?_⟩
  show PiTensorProduct.map (fun i => LinearMap.fst K (X.V i) (Y.V i))
      (PiTensorProduct.map (fun i => LinearMap.inl K (X.V i) (Y.V i)) X.t +
       PiTensorProduct.map (fun i => LinearMap.inr K (X.V i) (Y.V i)) Y.t) = X.t
  rw [map_add, ← LinearMap.comp_apply, ← PiTensorProduct.map_comp,
      ← LinearMap.comp_apply (PiTensorProduct.map _), ← PiTensorProduct.map_comp]
  have hfst_inl :
      (fun i => LinearMap.fst K (X.V i) (Y.V i) ∘ₗ LinearMap.inl K (X.V i) (Y.V i)) =
      fun i => (LinearMap.id : X.V i →ₗ[K] X.V i) := by
    funext i; ext x; rfl
  have hfst_inr :
      (fun i => LinearMap.fst K (X.V i) (Y.V i) ∘ₗ LinearMap.inr K (X.V i) (Y.V i)) =
      fun i => (0 : Y.V i →ₗ[K] X.V i) := by
    funext i; ext y; rfl
  rw [hfst_inl, hfst_inr, PiTensorProduct.map_id]
  show X.t + PiTensorProduct.map (fun i => (0 : Y.V i →ₗ[K] X.V i)) Y.t = X.t
  rw [map_zero_pitensor hd Y.t, add_zero]

private theorem restrict_add_right {d : ℕ} (hd : 0 < d) (X Y : TensorObj K d) :
    TensorObj.Restrict Y (TensorObj.add X Y) := by
  refine ⟨fun i => LinearMap.snd K (X.V i) (Y.V i), ?_⟩
  show PiTensorProduct.map (fun i => LinearMap.snd K (X.V i) (Y.V i))
      (PiTensorProduct.map (fun i => LinearMap.inl K (X.V i) (Y.V i)) X.t +
       PiTensorProduct.map (fun i => LinearMap.inr K (X.V i) (Y.V i)) Y.t) = Y.t
  rw [map_add, ← LinearMap.comp_apply, ← PiTensorProduct.map_comp,
      ← LinearMap.comp_apply (PiTensorProduct.map _), ← PiTensorProduct.map_comp]
  have hsnd_inl :
      (fun i => LinearMap.snd K (X.V i) (Y.V i) ∘ₗ LinearMap.inl K (X.V i) (Y.V i)) =
      fun i => (0 : X.V i →ₗ[K] Y.V i) := by
    funext i; ext x; rfl
  have hsnd_inr :
      (fun i => LinearMap.snd K (X.V i) (Y.V i) ∘ₗ LinearMap.inr K (X.V i) (Y.V i)) =
      fun i => (LinearMap.id : Y.V i →ₗ[K] Y.V i) := by
    funext i; ext y; rfl
  rw [hsnd_inl, hsnd_inr, PiTensorProduct.map_id]
  show PiTensorProduct.map (fun i => (0 : X.V i →ₗ[K] Y.V i)) X.t + Y.t = Y.t
  rw [map_zero_pitensor hd X.t, zero_add]

/-- Each summand of `bigAdd` is a restriction of the whole. -/
private theorem restrict_bigAdd_proj {d : ℕ} (hd : 0 < d) :
    ∀ {k : ℕ} (f : Fin k → TensorObj K d) (i : Fin k),
      TensorObj.Restrict (f i) (TensorObj.bigAdd f)
  | 0,     _, i => Fin.elim0 i
  | 1,     f, i => by
      match i with
      | ⟨0, _⟩ =>
        show TensorObj.Restrict (f ⟨0, _⟩) (f 0)
        exact restrict_refl _
  | k + 2, f, i => by
      show TensorObj.Restrict (f i)
        (TensorObj.add (f 0) (TensorObj.bigAdd (fun i => f i.succ)))
      match i with
      | ⟨0, _⟩ =>
        show TensorObj.Restrict (f ⟨0, _⟩)
          (TensorObj.add (f 0) (TensorObj.bigAdd (fun i => f i.succ)))
        exact restrict_add_left hd _ _
      | ⟨j+1, hj⟩ =>
        have hj' : j < k + 1 := by omega
        have hsub : TensorObj.Restrict ((fun i => f (Fin.succ i)) ⟨j, hj'⟩)
            (TensorObj.bigAdd (fun i => f (Fin.succ i))) :=
          restrict_bigAdd_proj hd (fun i => f (Fin.succ i)) ⟨j, hj'⟩
        have hr2 : TensorObj.Restrict (TensorObj.bigAdd (fun i => f (Fin.succ i)))
            (TensorObj.add (f 0) (TensorObj.bigAdd (fun i => f (Fin.succ i)))) :=
          restrict_add_right hd _ _
        have heq : (fun i => f (Fin.succ i)) ⟨j, hj'⟩ = f ⟨j+1, hj⟩ := by
          show f (Fin.succ ⟨j, hj'⟩) = f ⟨j+1, hj⟩
          rfl
        rw [← heq]
        exact restrict_trans hsub hr2

/-! ## (2) Finrank of kron-power modes -/

private theorem finrank_kron_V {d : ℕ} (X Y : TensorObj K d) (i : Fin d) :
    Module.finrank K ((TensorObj.kron X Y).V i) =
      Module.finrank K (X.V i) * Module.finrank K (Y.V i) := by
  show Module.finrank K (X.V i ⊗[K] Y.V i) = _
  exact Module.finrank_tensorProduct

private theorem finrank_oneObj_V {d : ℕ} (i : Fin d) :
    Module.finrank K ((TensorObj.oneObj : TensorObj K d).V i) = 1 := by
  show Module.finrank K K = 1
  exact Module.finrank_self K

private theorem finrank_kronPow_V {d : ℕ} (T : TensorObj K d) (i : Fin d) :
    ∀ N : ℕ, Module.finrank K ((TensorObj.kronPow T N).V i) =
      (Module.finrank K (T.V i)) ^ N
  | 0 => by
      show Module.finrank K ((TensorObj.oneObj : TensorObj K d).V i) = _
      rw [finrank_oneObj_V]; ring
  | N + 1 => by
      show Module.finrank K ((TensorObj.kron T (TensorObj.kronPow T N)).V i) = _
      rw [finrank_kron_V, finrank_kronPow_V T i N]; ring

/-! ## (3) Mode-`j` flat-rank ≤ codomain-finrank. -/

/-- The codomain of `flatteningMap σ X` has `finrank = ∏_{i ∈ Sᶜ} finrank K (X.V i)`. -/
private theorem finrank_flatteningMap_codomain {d : ℕ} (σ : Split (Fin d)) (X : TensorObj K d) :
    Module.finrank K (PiTensorProduct K (fun i : Sc σ => X.V i)) =
      ∏ i : Sc σ, Module.finrank K (X.V i) := by
  classical
  haveI : ∀ i : Sc σ, Module.Free K (X.V i) := fun _ => inferInstance
  haveI : ∀ i : Sc σ, Module.Finite K (X.V i) := fun _ => inferInstance
  set b : Basis (∀ i : Sc σ, Module.Free.ChooseBasisIndex K (X.V i)) K
      (PiTensorProduct K (fun i : Sc σ => X.V i)) :=
    Basis.piTensorProduct (fun i => Module.Free.chooseBasis K (X.V i))
  rw [Module.finrank_eq_card_basis b]
  rw [Fintype.card_pi]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [Module.finrank_eq_card_chooseBasisIndex]

/-- Flat rank is bounded by the codomain dimension. -/
private theorem flatteningRank_le_finrank_cod {d : ℕ} (σ : Split (Fin d)) (X : TensorObj K d) :
    flatteningRank σ X ≤ ∏ i : Sc σ, Module.finrank K (X.V i) := by
  rw [← finrank_flatteningMap_codomain]
  unfold flatteningRank
  haveI : ∀ i : Sc σ, Module.Free K (X.V i) := fun _ => inferInstance
  haveI : ∀ i : Sc σ, Module.Finite K (X.V i) := fun _ => inferInstance
  haveI : FiniteDimensional K (PiTensorProduct K (fun i : Sc σ => X.V i)) :=
    Module.Finite.of_basis (Basis.piTensorProduct (fun i => Module.Free.chooseBasis K (X.V i)))
  exact Submodule.finrank_le _

/-- Flat rank of `T.kronPow N` at any split: bounded by the product of the `Sᶜ`-mode
dimensions, each raised to the `N`th power. -/
private theorem flatteningRank_kronPow_le {d : ℕ} (σ : Split (Fin d))
    (T : TensorObj K d) (N : ℕ) :
    flatteningRank σ (TensorObj.kronPow T N) ≤
      ∏ i : Sc σ, (Module.finrank K (T.V i)) ^ N := by
  refine (flatteningRank_le_finrank_cod _ _).trans ?_
  refine Finset.prod_le_prod (fun _ _ => Nat.zero_le _) (fun i _ => ?_)
  rw [finrank_kronPow_V]

/-! ## (4) Identify the complement of each singleton split. -/

/-- `Sᶜ` of `diagSplit (d := 3)` = `{(1 : Fin 3), (2 : Fin 3)}`. -/
private theorem diagSplit3_Sc :
    Sc (MME.diagSplit (d := 3) (by norm_num)) =
      ({(1 : Fin 3), (2 : Fin 3)} : Finset (Fin 3)) := by
  decide

private theorem split1_Sc :
    Sc (MME.split1) = ({(0 : Fin 3), (2 : Fin 3)} : Finset (Fin 3)) := by
  decide

private theorem split2_Sc :
    Sc (MME.split2) = ({(0 : Fin 3), (1 : Fin 3)} : Finset (Fin 3)) := by
  decide

/-! ## (5) Mode-cyclic flattening dimension bound: product over complement. -/

private theorem prod_Sc_diagSplit3 (T : TensorObj K 3) :
    ∏ i : Sc (MME.diagSplit (d := 3) (by norm_num)), Module.finrank K (T.V i.val) =
      Module.finrank K (T.V 1) * Module.finrank K (T.V 2) := by
  classical
  rw [Finset.prod_coe_sort _ (fun i => Module.finrank K (T.V i))]
  rw [diagSplit3_Sc]
  rw [show ({(1 : Fin 3), (2 : Fin 3)} : Finset (Fin 3)) =
        insert (1 : Fin 3) {(2 : Fin 3)} from rfl]
  rw [Finset.prod_insert (by decide), Finset.prod_singleton]

private theorem prod_Sc_split1 (T : TensorObj K 3) :
    ∏ i : Sc (MME.split1), Module.finrank K (T.V i.val) =
      Module.finrank K (T.V 0) * Module.finrank K (T.V 2) := by
  classical
  rw [Finset.prod_coe_sort _ (fun i => Module.finrank K (T.V i))]
  rw [split1_Sc]
  rw [show ({(0 : Fin 3), (2 : Fin 3)} : Finset (Fin 3)) =
        insert (0 : Fin 3) {(2 : Fin 3)} from rfl]
  rw [Finset.prod_insert (by decide), Finset.prod_singleton]

private theorem prod_Sc_split2 (T : TensorObj K 3) :
    ∏ i : Sc (MME.split2), Module.finrank K (T.V i.val) =
      Module.finrank K (T.V 0) * Module.finrank K (T.V 1) := by
  classical
  rw [Finset.prod_coe_sort _ (fun i => Module.finrank K (T.V i))]
  rw [split2_Sc]
  rw [show ({(0 : Fin 3), (1 : Fin 3)} : Finset (Fin 3)) =
        insert (0 : Fin 3) {(1 : Fin 3)} from rfl]
  rw [Finset.prod_insert (by decide), Finset.prod_singleton]

/-! ## (6) Triple flat-rank bound on each MMObj summand. -/

/-- For each MMObj summand restricted into `T.kronPow N`, with all dims ≥ 1, we have
`(aᵢ * bᵢ * cᵢ)^2 ≤ D^{2N}` where `D = (finrank V_0)(finrank V_1)(finrank V_2)`. -/
private theorem cube_prod_bound (T : TensorObj K 3) (N : ℕ)
    (a b c : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (hres : TensorObj.Restrict (MMObj K a b c) (TensorObj.kronPow T N)) :
    (a * b * c) * (a * b * c) ≤
      (Module.finrank K (T.V 0) * Module.finrank K (T.V 1) * Module.finrank K (T.V 2)) ^ N *
        (Module.finrank K (T.V 0) * Module.finrank K (T.V 1) * Module.finrank K (T.V 2)) ^ N := by
  -- Use the three flat-rank lower bounds (cyclic).
  -- Prod-rewrite helpers.
  have hprod0 :
      ∏ i : Sc (MME.diagSplit (d := 3) (by norm_num)),
          (Module.finrank K (T.V i.val)) ^ N =
        Module.finrank K (T.V 1) ^ N * Module.finrank K (T.V 2) ^ N := by
    classical
    rw [Finset.prod_coe_sort _ (fun i => Module.finrank K (T.V i) ^ N)]
    rw [diagSplit3_Sc]
    rw [show ({(1 : Fin 3), (2 : Fin 3)} : Finset (Fin 3)) =
          insert (1 : Fin 3) {(2 : Fin 3)} from rfl]
    rw [Finset.prod_insert (by decide), Finset.prod_singleton]
  have hprod1 :
      ∏ i : Sc (MME.split1), (Module.finrank K (T.V i.val)) ^ N =
        Module.finrank K (T.V 0) ^ N * Module.finrank K (T.V 2) ^ N := by
    classical
    rw [Finset.prod_coe_sort _ (fun i => Module.finrank K (T.V i) ^ N)]
    rw [split1_Sc]
    rw [show ({(0 : Fin 3), (2 : Fin 3)} : Finset (Fin 3)) =
          insert (0 : Fin 3) {(2 : Fin 3)} from rfl]
    rw [Finset.prod_insert (by decide), Finset.prod_singleton]
  have hprod2 :
      ∏ i : Sc (MME.split2), (Module.finrank K (T.V i.val)) ^ N =
        Module.finrank K (T.V 0) ^ N * Module.finrank K (T.V 1) ^ N := by
    classical
    rw [Finset.prod_coe_sort _ (fun i => Module.finrank K (T.V i) ^ N)]
    rw [split2_Sc]
    rw [show ({(0 : Fin 3), (1 : Fin 3)} : Finset (Fin 3)) =
          insert (0 : Fin 3) {(1 : Fin 3)} from rfl]
    rw [Finset.prod_insert (by decide), Finset.prod_singleton]
  have hab : a * b ≤
      Module.finrank K (T.V 1) ^ N * Module.finrank K (T.V 2) ^ N := by
    have hMM := mme_flatteningRank_MMObj_ab (K := K) a b c hc
    have hmono := flatteningRank_mono (MME.diagSplit (d := 3) (by norm_num)) hres
    have hkp := flatteningRank_kronPow_le (MME.diagSplit (d := 3) (by norm_num)) T N
    exact ((hMM.trans hmono).trans hkp).trans_eq hprod0
  have hbc : b * c ≤
      Module.finrank K (T.V 0) ^ N * Module.finrank K (T.V 2) ^ N := by
    have hMM := mme_flatteningRank_MMObj_bc (K := K) a b c ha
    have hmono := flatteningRank_mono MME.split1 hres
    have hkp := flatteningRank_kronPow_le MME.split1 T N
    exact ((hMM.trans hmono).trans hkp).trans_eq hprod1
  have hca : c * a ≤
      Module.finrank K (T.V 0) ^ N * Module.finrank K (T.V 1) ^ N := by
    have hMM := mme_flatteningRank_MMObj_ca (K := K) a b c hb
    have hmono := flatteningRank_mono MME.split2 hres
    have hkp := flatteningRank_kronPow_le MME.split2 T N
    exact ((hMM.trans hmono).trans hkp).trans_eq hprod2
  -- Now multiply.
  have hmul := Nat.mul_le_mul (Nat.mul_le_mul hab hbc) hca
  calc (a * b * c) * (a * b * c)
      = (a * b) * (b * c) * (c * a) := by ring
    _ ≤ (Module.finrank K (T.V 1) ^ N * Module.finrank K (T.V 2) ^ N) *
        (Module.finrank K (T.V 0) ^ N * Module.finrank K (T.V 2) ^ N) *
        (Module.finrank K (T.V 0) ^ N * Module.finrank K (T.V 1) ^ N) := hmul
    _ = (Module.finrank K (T.V 0) * Module.finrank K (T.V 1) *
            Module.finrank K (T.V 2)) ^ N *
        (Module.finrank K (T.V 0) * Module.finrank K (T.V 1) *
            Module.finrank K (T.V 2)) ^ N := by
        rw [← mul_pow, ← mul_pow]
        ring

end MMESubrankPolyGe

-- ============================================================================
-- Main theorem
-- ============================================================================

open MMESubrankPolyGe

/-- The bound `M = D + 1` on the polynomial-subrank-capacity defining set. -/
private noncomputable def boundM {K : Type u} [Field K] (T : TensorObj K 3) : ℕ :=
  Module.finrank K (T.V 0) * Module.finrank K (T.V 1) * Module.finrank K (T.V 2) + 1

namespace MMESubrankPolyGe

/-- Square-root monotonicity for naturals. -/
private theorem nat_le_of_sq_le_sq {a b : ℕ} (h : a * a ≤ b * b) : a ≤ b := by
  by_contra hab
  push_neg at hab
  have : b * b < a * a :=
    Nat.mul_lt_mul_of_lt_of_le hab (Nat.le_of_lt hab) (Nat.lt_of_le_of_lt (Nat.zero_le b) hab)
  omega

/-- Per-summand bound: `(aᵢbᵢcᵢ)^{1/3} ≤ (D+1)^N` whenever a restriction into `T.kronPow N` is given. -/
private theorem per_summand_bound {K : Type u} [Field K] (T : TensorObj K 3) (N : ℕ)
    (a b c : ℕ)
    (hres : TensorObj.Restrict (MMObj K a b c) (TensorObj.kronPow T N)) :
    ((a * b * c : ℕ) : ℝ) ^ ((1 : ℝ) / 3) ≤ ((boundM T : ℕ) : ℝ) ^ N := by
  set D : ℕ := Module.finrank K (T.V 0) * Module.finrank K (T.V 1) * Module.finrank K (T.V 2)
    with hD
  have hM : (boundM T : ℕ) = D + 1 := rfl
  by_cases habc : a * b * c = 0
  · rw [habc]
    push_cast
    rw [Real.zero_rpow (by norm_num : (1 : ℝ) / 3 ≠ 0)]
    positivity
  · have habc_pos : 1 ≤ a * b * c := Nat.one_le_iff_ne_zero.mpr habc
    have ha : 1 ≤ a := by
      by_contra h
      push_neg at h
      interval_cases a
      simp at habc
    have hb : 1 ≤ b := by
      by_contra h
      push_neg at h
      interval_cases b
      simp at habc
    have hc : 1 ≤ c := by
      by_contra h
      push_neg at h
      interval_cases c
      simp at habc
    have hcube := cube_prod_bound T N a b c ha hb hc hres
    have habc_le : a * b * c ≤ D ^ N := nat_le_of_sq_le_sq hcube
    have habc_R_pos : (1 : ℝ) ≤ ((a * b * c : ℕ) : ℝ) := by
      exact_mod_cast habc_pos
    have hcuberoot : ((a * b * c : ℕ) : ℝ) ^ ((1 : ℝ) / 3) ≤ ((a * b * c : ℕ) : ℝ) := by
      have := Real.rpow_le_rpow_of_exponent_le habc_R_pos (by norm_num : (1 : ℝ) / 3 ≤ 1)
      simpa [Real.rpow_one] using this
    have habc_R_le : ((a * b * c : ℕ) : ℝ) ≤ ((D ^ N : ℕ) : ℝ) := by
      exact_mod_cast habc_le
    have hDle : ((D ^ N : ℕ) : ℝ) ≤ ((boundM T : ℕ) : ℝ) ^ N := by
      have hD_le : (D : ℝ) ≤ ((boundM T : ℕ) : ℝ) := by
        rw [hM]; push_cast; linarith
      have : (D : ℝ) ^ N ≤ ((boundM T : ℕ) : ℝ) ^ N :=
        pow_le_pow_left₀ (by positivity) hD_le N
      simpa [Nat.cast_pow] using this
    linarith [hcuberoot, habc_R_le, hDle]

end MMESubrankPolyGe

theorem solution
    {K : Type u} [Field K] (T : TensorObj K 3)
    (V : ℝ) (hV : 1 ≤ V)
    (hwit : ∃ c : ℝ,
      ∀ ε > (0 : ℝ), ∃ᶠ (N : ℕ) in atTop,
        ∃ (k : ℕ) (a b c' : Fin k → ℕ),
          (k : ℝ) ≤ ((N : ℝ) + 1) ^ c ∧
          TensorObj.Restrict
            (TensorObj.bigAdd (fun i => MMObj K (a i) (b i) (c' i)))
            (T.kronPow N)
          ∧ V ^ N * (1 - ε) ≤ ∑ i, ((a i * b i * c' i : ℕ) : ℝ) ^ ((1 : ℝ) / 3)) :
    V ≤ subrankCapacityPoly T := by
  -- Set up.
  set M : ℝ := ((boundM T : ℕ) : ℝ) with hMdef
  have hM_pos : (1 : ℝ) ≤ M := by
    rw [hMdef]
    have : (1 : ℕ) ≤ boundM T := by unfold boundM; omega
    exact_mod_cast this
  have hM_pos' : (0 : ℝ) < M := by linarith
  -- subrankCapacityPoly T = sSup S
  set S : Set ℝ := { V : ℝ | 1 ≤ V ∧ ∃ c : ℝ,
    ∀ ε > (0 : ℝ), ∃ᶠ (N : ℕ) in atTop,
      ∃ (k : ℕ) (a b c' : Fin k → ℕ),
        (k : ℝ) ≤ ((N : ℝ) + 1) ^ c ∧
        TensorObj.Restrict
          (TensorObj.bigAdd (fun i => MMObj K (a i) (b i) (c' i)))
          (T.kronPow N)
        ∧ V ^ N * (1 - ε) ≤ ∑ i, ((a i * b i * c' i : ℕ) : ℝ) ^ ((1 : ℝ) / 3) } with hSdef
  have hVmem : V ∈ S := ⟨hV, hwit⟩
  have hSup_eq : subrankCapacityPoly T = sSup S := rfl
  rw [hSup_eq]
  -- BddAbove key step: every V' ∈ S is ≤ M.
  have hbdd : BddAbove S := by
    refine ⟨M, ?_⟩
    rintro V' ⟨hV'1, c, hVwit⟩
    -- Show V' ≤ M. By contradiction: suppose V' > M.
    by_contra hlt
    push_neg at hlt
    -- Now V' > M ≥ 1, so log V' > log M and log(V'/M) > 0.
    have hV'_pos : (0 : ℝ) < V' := by linarith
    have hV'_gt_one : (1 : ℝ) < V' := by linarith
    set r : ℝ := V' / M with hr_def
    have hr_pos : (0 : ℝ) < r := by positivity
    have hr_gt_one : (1 : ℝ) < r := by
      rw [hr_def]
      exact (one_lt_div hM_pos').mpr hlt
    -- We will derive a contradiction using ε = 1/2.
    have hε : (0 : ℝ) < 1 / 2 := by norm_num
    have hfreq := hVwit (1/2) hε
    -- Build an eventually-true contradicting statement:
    --   ∀ᶠ N in atTop, ¬ (V'^N · (1/2) ≤ (N+1)^c · M^N).
    -- Equivalently: V'^N · (1/2) > (N+1)^c · M^N for large N.
    -- Use `(N+1)^c = o(r^N)`.
    -- Cast (N : ℕ) → (N : ℝ) and use `isLittleO_rpow_exp_pos_mul_atTop`.
    have hlogr : (0 : ℝ) < Real.log r := Real.log_pos hr_gt_one
    -- The fact (x : ℝ)^c = o(exp(log r · x)) = o(r^x) at x → ∞.
    have hlito : (fun x : ℝ => x ^ c) =o[atTop] (fun x : ℝ => Real.exp (Real.log r * x)) :=
      isLittleO_rpow_exp_pos_mul_atTop c hlogr
    -- Convert exp(log r · x) = r^x.  In Mathlib: r^x = exp(x · log r).
    have hexp_eq : ∀ x : ℝ, Real.exp (Real.log r * x) = r ^ x := by
      intro x
      rw [Real.rpow_def_of_pos hr_pos x, mul_comm]
    have hlito2 : (fun x : ℝ => x ^ c) =o[atTop] (fun x : ℝ => r ^ x) := by
      convert hlito using 1
      ext x; exact (hexp_eq x).symm
    -- Pull this back to ℕ via tendsto_natCast_atTop_atTop.
    have hlito_nat :
        (fun N : ℕ => ((N : ℝ) + 1) ^ c) =o[atTop] (fun N : ℕ => r ^ ((N : ℝ) + 1)) := by
      -- ((N : ℝ) + 1)^c = (cast (N+1))^c. Use shift by 1.
      have htends : Tendsto (fun N : ℕ => ((N : ℝ) + 1)) atTop atTop := by
        have h0 : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop :=
          tendsto_natCast_atTop_atTop
        exact h0.atTop_add tendsto_const_nhds
      exact hlito2.comp_tendsto htends
    -- From hlito_nat: ∀ ε' > 0, ∃ᶠ K eventually, |(N+1)^c| ≤ ε' · |r^(N+1)|.
    -- We want: ∀ᶠ N, 4 · ((N+1)^c) ≤ r^(N+1) (say, for chosen tolerance).
    -- Use isLittleO.eventually_le with bound (1/4):
    have hevent : ∀ᶠ N : ℕ in atTop,
        ((N : ℝ) + 1) ^ c ≤ (1 / 4) * r ^ ((N : ℝ) + 1) := by
      -- isLittleO definition: ∀ ε > 0, eventually |f| ≤ ε |g|.
      have := hlito_nat.def (by norm_num : (0 : ℝ) < 1 / 4)
      filter_upwards [this] with N hN
      -- |((N+1)^c)| ≤ (1/4) · |r^(N+1)|
      have h1 : (0 : ℝ) ≤ ((N : ℝ) + 1) ^ c := by positivity
      have h2 : (0 : ℝ) ≤ r ^ ((N : ℝ) + 1) := Real.rpow_nonneg hr_pos.le _
      have := hN
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg h1, abs_of_nonneg h2] at this
      exact this
    -- Now combine with the frequent witness: get a contradiction for some N.
    -- We want: V'^N · (1/2) ≤ ∑ ≤ (N+1)^c · M^N. So V'^N · (1/2) ≤ (N+1)^c · M^N.
    -- And: (N+1)^c ≤ (1/4) r^(N+1) = (1/4) r · r^N (eventually).
    -- So (N+1)^c · M^N ≤ (1/4) r · r^N · M^N = (1/4) r · (V'/M)^N · M^N
    --                  = (1/4) r · V'^N.
    -- Hence V'^N · (1/2) ≤ (1/4) r · V'^N, i.e., 2 ≤ r, i.e., V'/M ≥ 2.
    -- Hmm we don't have V'/M ≥ 2 a priori, so the contradiction isn't immediate.
    -- Let me redo with sharper bound: ε' = 1/(2 r) (so RHS becomes V'^N · (1/2)).
    -- Actually we just need bound 1/(2 r) instead of 1/4:
    have hevent2 : ∀ᶠ N : ℕ in atTop,
        ((N : ℝ) + 1) ^ c ≤ (1 / (4 * r)) * r ^ ((N : ℝ) + 1) := by
      have htol : (0 : ℝ) < 1 / (4 * r) := by positivity
      have := hlito_nat.def htol
      filter_upwards [this] with N hN
      have h1 : (0 : ℝ) ≤ ((N : ℝ) + 1) ^ c := by positivity
      have h2 : (0 : ℝ) ≤ r ^ ((N : ℝ) + 1) := Real.rpow_nonneg hr_pos.le _
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg h1, abs_of_nonneg h2] at hN
      exact hN
    -- Also need N > 0 to make V'^N well-defined (positive). Use atTop_eventually_one.
    have hev_pos : ∀ᶠ N : ℕ in atTop, 1 ≤ N := eventually_ge_atTop 1
    have hcombined := (hfreq.and_eventually hevent2).and_eventually hev_pos
    obtain ⟨N, ⟨⟨k, a, b, c', hk, hres, hsum⟩, hbnd⟩, hN1⟩ := hcombined.exists
    -- Derivation of contradiction.
    -- Step A: each summand (aᵢbᵢcᵢ)^{1/3} ≤ M^N.
    have hMpow_pos : (0 : ℝ) < M ^ N := pow_pos hM_pos' N
    -- Each MMObj_i is a restriction of T.kronPow N via bigAdd projection + trans.
    have hd_pos : (0 : ℕ) < 3 := by norm_num
    have h_each_res : ∀ i : Fin k,
        TensorObj.Restrict (MMObj K (a i) (b i) (c' i)) (T.kronPow N) := by
      intro i
      have hsub := restrict_bigAdd_proj hd_pos (fun i => MMObj K (a i) (b i) (c' i)) i
      exact restrict_trans hsub hres
    have h_each_bound : ∀ i : Fin k,
        ((a i * b i * c' i : ℕ) : ℝ) ^ ((1 : ℝ) / 3) ≤ M ^ N := by
      intro i
      have := per_summand_bound T N (a i) (b i) (c' i) (h_each_res i)
      simpa [hMdef] using this
    -- ∑ᵢ (aᵢbᵢcᵢ)^{1/3} ≤ k · M^N
    have hsum_le : ∑ i, ((a i * b i * c' i : ℕ) : ℝ) ^ ((1 : ℝ) / 3) ≤ (k : ℝ) * M ^ N := by
      calc ∑ i, ((a i * b i * c' i : ℕ) : ℝ) ^ ((1 : ℝ) / 3)
          ≤ ∑ _i : Fin k, M ^ N :=
            Finset.sum_le_sum (fun i _ => h_each_bound i)
        _ = (k : ℝ) * M ^ N := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
            ring
    -- ∑ ≤ (N+1)^c · M^N
    have hk_pos : (0 : ℝ) ≤ (k : ℝ) := by positivity
    have h_sum_poly : ∑ i, ((a i * b i * c' i : ℕ) : ℝ) ^ ((1 : ℝ) / 3) ≤
        ((N : ℝ) + 1) ^ c * M ^ N := by
      apply hsum_le.trans
      apply (mul_le_mul_of_nonneg_right hk hMpow_pos.le)
    -- (N+1)^c · M^N ≤ (1/(4 r)) · r^(N+1) · M^N
    have hpoly_le : ((N : ℝ) + 1) ^ c * M ^ N ≤
        (1 / (4 * r)) * r ^ ((N : ℝ) + 1) * M ^ N := by
      apply mul_le_mul_of_nonneg_right hbnd hMpow_pos.le
    -- (1/(4r)) · r^(N+1) · M^N = (r^N · M^N) / 4
    -- r^(N+1) = r · r^N
    have hr_split : r ^ ((N : ℝ) + 1) = r * r ^ (N : ℝ) := by
      rw [Real.rpow_add hr_pos]; ring_nf; simp
    -- r^N (real) = r^N (nat) since N is nat.
    have hr_natpow : r ^ (N : ℝ) = r ^ N := by
      exact (Real.rpow_natCast r N)
    have hrM_pow : r ^ N * M ^ N = V' ^ N := by
      have : r * M = V' := by rw [hr_def]; field_simp
      rw [← mul_pow, this]
    -- Combine: ∑ ≤ V'^N / 4
    have h_sum_quartile : ∑ i, ((a i * b i * c' i : ℕ) : ℝ) ^ ((1 : ℝ) / 3) ≤
        V' ^ N / 4 := by
      apply h_sum_poly.trans
      apply hpoly_le.trans
      rw [hr_split, hr_natpow]
      -- Goal: (1 / (4 * r)) * (r * r ^ N) * M ^ N ≤ V' ^ N / 4
      rw [← hrM_pow]
      -- Goal: (1 / (4 * r)) * (r * r ^ N) * M ^ N ≤ r ^ N * M ^ N / 4
      have hr_ne : r ≠ 0 := ne_of_gt hr_pos
      have heq : (1 / (4 * r)) * (r * r ^ N) * M ^ N = r ^ N * M ^ N / 4 := by
        field_simp
      rw [heq]
    -- hsum: V'^N · (1/2) ≤ ∑
    -- So V'^N · (1/2) ≤ V'^N / 4. Since V' > 0 (V' ≥ 1), this is a contradiction.
    have hV'N_pos : (0 : ℝ) < V' ^ N := pow_pos hV'_pos N
    -- hsum has the form V'^N * (1 - 1/2). Normalize to (1/2).
    have hsum' : V' ^ N * (1/2) ≤ ∑ i, ((a i * b i * c' i : ℕ) : ℝ) ^ ((1 : ℝ) / 3) := by
      have heq : (1 : ℝ) - 1/2 = 1/2 := by norm_num
      rw [heq] at hsum
      exact hsum
    have hcontra : V' ^ N * (1 / 2) ≤ V' ^ N / 4 := hsum'.trans h_sum_quartile
    have hstrict : V' ^ N / 4 < V' ^ N * (1 / 2) := by
      have h1 : V' ^ N * (1 / 4) < V' ^ N * (1 / 2) := by
        nlinarith [hV'N_pos]
      linarith
    linarith
  exact le_csSup hbdd hVmem
