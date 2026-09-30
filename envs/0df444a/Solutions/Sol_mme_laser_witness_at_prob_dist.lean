-- Prove2me | solution 1 for mme_laser_witness_at_prob_dist
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-06T12:19:01.918028+00:00
-- url     : https://prove2.me/submissions/e09cbcb8-1e96-4012-b6a1-82ebff764a10

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Definitions.Def_mme_laser_pattern
import Definitions.Def_mme_subrank_capacity_poly
import Definitions.Def_mme_tensor_type_grading
import Definitions.Def_mme_tensor_rank
open MME BigOperators

/-! ### Auxiliary facts about the zero tensor object, direct sums, and `MMTensor` -/

/-- The `PiTensorProduct.map` of the zero family of linear maps is zero (the index type
`Fin 3` is nonempty). -/
theorem lwd_map_zero_family.{u} {K : Type u} [Field K] {M N : Fin 3 → Type u}
    [∀ i, AddCommGroup (M i)] [∀ i, Module K (M i)]
    [∀ i, AddCommGroup (N i)] [∀ i, Module K (N i)]
    (x : PiTensorProduct K M) :
    PiTensorProduct.map (fun i => (0 : M i →ₗ[K] N i)) x = 0 := by
  have h : PiTensorProduct.map (fun i => (0 : M i →ₗ[K] N i)) = 0 := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro v
    simp only [LinearMap.compMultilinearMap_apply, PiTensorProduct.map_tprod,
      LinearMap.zero_apply]
    exact MultilinearMap.map_zero _
  rw [h]
  rfl

/-- If the tensor of a direct sum `X ⊕ Y` vanishes, so do the tensors of both summands
(project with `fst`/`snd`). -/
theorem lwd_add_t_eq_zero.{u} {K : Type u} [Field K] (X Y : TensorObj K 3)
    (h : (TensorObj.add X Y).t = 0) : X.t = 0 ∧ Y.t = 0 := by
  have h' : PiTensorProduct.map (fun i => LinearMap.inl K (X.V i) (Y.V i)) X.t +
      PiTensorProduct.map (fun i => LinearMap.inr K (X.V i) (Y.V i)) Y.t = 0 := h
  constructor
  · have h1 := congrArg (PiTensorProduct.map (fun i => LinearMap.fst K (X.V i) (Y.V i))) h'
    rw [map_add, map_zero, ← LinearMap.comp_apply, ← LinearMap.comp_apply,
      ← PiTensorProduct.map_comp, ← PiTensorProduct.map_comp] at h1
    simp only [LinearMap.fst_comp_inl, LinearMap.fst_comp_inr, PiTensorProduct.map_id,
      LinearMap.id_apply, lwd_map_zero_family, add_zero] at h1
    exact h1
  · have h1 := congrArg (PiTensorProduct.map (fun i => LinearMap.snd K (X.V i) (Y.V i))) h'
    rw [map_add, map_zero, ← LinearMap.comp_apply, ← LinearMap.comp_apply,
      ← PiTensorProduct.map_comp, ← PiTensorProduct.map_comp] at h1
    simp only [LinearMap.snd_comp_inl, LinearMap.snd_comp_inr, PiTensorProduct.map_id,
      LinearMap.id_apply, lwd_map_zero_family, zero_add] at h1
    exact h1

/-- If the tensor of a finite direct sum vanishes, every summand's tensor vanishes. -/
theorem lwd_bigAdd_t_eq_zero.{u} {K : Type u} [Field K] :
    ∀ {k : ℕ} (f : Fin k → TensorObj K 3),
      (TensorObj.bigAdd f).t = 0 → ∀ i, (f i).t = 0
  | 0, _, _, i => Fin.elim0 i
  | 1, f, h, i => by
      have hi : i = 0 := Subsingleton.elim i 0
      subst hi
      exact h
  | k + 2, f, h, i => by
      have h' : (TensorObj.add (f 0) (TensorObj.bigAdd (fun j => f j.succ))).t = 0 := h
      obtain ⟨h0, h1⟩ := lwd_add_t_eq_zero _ _ h'
      refine Fin.cases h0 (fun j => ?_) i
      exact lwd_bigAdd_t_eq_zero (fun j => f j.succ) h1 j

/-- Positive Kronecker powers of the zero tensor object have zero tensor. -/
theorem lwd_kronPow_zeroObj_succ_t.{u} {K : Type u} [Field K] (N : ℕ) :
    ((TensorObj.zeroObj : TensorObj K 3).kronPow (N + 1)).t = 0 := by
  show interchange (TensorObj.zeroObj : TensorObj K 3).t
    ((TensorObj.zeroObj : TensorObj K 3).kronPow N).t = 0
  show interchange (0 : PiTensorProduct K (TensorObj.zeroObj : TensorObj K 3).V) _ = 0
  rw [map_zero]
  rfl

/-- Evaluation of the three mode spaces of `MM(a,b,c)` at the corner coordinates. -/
def lwd_cornerEval.{u} (K : Type u) [Field K] (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    ∀ s : Fin 3, MMSpace K a b c s →ₗ[K] K
  | ⟨0, _⟩ => LinearMap.proj (⟨0, ha⟩, ⟨0, hb⟩)
  | ⟨1, _⟩ => LinearMap.proj (⟨0, hb⟩, ⟨0, hc⟩)
  | ⟨2, _⟩ => LinearMap.proj (⟨0, hc⟩, ⟨0, ha⟩)

/-- The matrix-multiplication tensor with positive dimensions is nonzero: the corner
functional `e_{00} ⊗ e_{00} ⊗ e_{00}` evaluates it to `1`. -/
theorem lwd_MMTensor_ne_zero.{u} {K : Type u} [Field K] (a b c : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : MMTensor K a b c ≠ 0 := by
  intro h0
  let φ : MultilinearMap K (MMSpace K a b c) K :=
    (MultilinearMap.mkPiAlgebra K (Fin 3) K).compLinearMap (lwd_cornerEval K a b c ha hb hc)
  have h1 := congrArg (PiTensorProduct.lift φ) h0
  rw [map_zero] at h1
  unfold MMTensor at h1
  simp only [map_sum, PiTensorProduct.lift.tprod, φ, MultilinearMap.compLinearMap_apply,
    MultilinearMap.mkPiAlgebra_apply, Fin.prod_univ_three] at h1
  simp [lwd_cornerEval, Pi.single_apply, Prod.ext_iff, Fin.ext_iff] at h1
  have hx0 : ∀ {n : ℕ} (hn : 0 < n) (x : Fin n), x ≠ ⟨0, hn⟩ → ((0 : ℕ) = (x : ℕ)) = False := by
    intro n hn x hx
    exact eq_false (fun h => hx (Fin.ext h.symm))
  rw [Finset.sum_eq_single (⟨0, ha⟩ : Fin a) (fun x _ hx => by simp [hx0 ha x hx])
      (fun h => absurd (Finset.mem_univ _) h),
    Finset.sum_eq_single (⟨0, hb⟩ : Fin b) (fun x _ hx => by simp [hx0 hb x hx])
      (fun h => absurd (Finset.mem_univ _) h),
    Finset.sum_eq_single (⟨0, hc⟩ : Fin c) (fun x _ hx => by simp [hx0 hc x hx])
      (fun h => absurd (Finset.mem_univ _) h)] at h1
  simp at h1

/-- The polynomial-witness subrank capacity of the zero tensor object is `0`: no positive
Kronecker power of it restricts to a nonzero direct sum of matrix-multiplication tensors, so
the defining set is empty and `sSup ∅ = 0` in `ℝ`. -/
theorem lwd_subrankCapacityPoly_zeroObj.{u} {K : Type u} [Field K] :
    subrankCapacityPoly (TensorObj.zeroObj : TensorObj K 3) = 0 := by
  unfold subrankCapacityPoly
  have hempty : { V : ℝ | 1 ≤ V ∧ ∃ c : ℝ,
      ∀ ε > (0 : ℝ), ∃ᶠ (N : ℕ) in Filter.atTop,
        ∃ (k : ℕ) (a b c' : Fin k → ℕ),
          (k : ℝ) ≤ ((N : ℝ) + 1) ^ c ∧
          TensorObj.Restrict
            (TensorObj.bigAdd (fun i => MMObj K (a i) (b i) (c' i)))
            ((TensorObj.zeroObj : TensorObj K 3).kronPow N)
          ∧ V ^ N * (1 - ε) ≤ ∑ i, ((a i * b i * c' i : ℕ) : ℝ) ^ ((1 : ℝ) / 3) } = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro V ⟨hV1, c, hc⟩
    obtain ⟨N, hN, k, a, b, c', -, ⟨f, hf⟩, hsum⟩ :=
      Filter.frequently_atTop.mp (hc (1 / 2) (by norm_num)) 1
    obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
    rw [lwd_kronPow_zeroObj_succ_t, map_zero] at hf
    have hall := lwd_bigAdd_t_eq_zero _ hf.symm
    have hzero : ∀ i, ((a i * b i * c' i : ℕ) : ℝ) ^ ((1 : ℝ) / 3) = 0 := by
      intro i
      have hi : MMTensor K (a i) (b i) (c' i) = 0 := hall i
      have hprod : a i * b i * c' i = 0 := by
        by_contra hne
        have ha : 0 < a i := Nat.pos_of_ne_zero (fun h => hne (by simp [h]))
        have hb : 0 < b i := Nat.pos_of_ne_zero (fun h => hne (by simp [h]))
        have hc' : 0 < c' i := Nat.pos_of_ne_zero (fun h => hne (by simp [h]))
        exact lwd_MMTensor_ne_zero _ _ _ ha hb hc' hi
      rw [hprod]
      simp
    rw [Finset.sum_eq_zero (fun i _ => hzero i)] at hsum
    have hpow : (1 : ℝ) ≤ V ^ (M + 1) := one_le_pow₀ hV1
    linarith
  rw [hempty, Real.sSup_empty]

/-- The trivial one-class grading of the zero tensor object. -/
noncomputable def lwd_trivialGrading (K : Type) [Field K] :
    (TensorObj.zeroObj : TensorObj K 3).TypeGrading 1 where
  decomp _ _ := ⊤
  is_internal i := by
    refine DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
      (iSupIndep_subsingleton _) ?_
    simp

theorem solution : ¬ (∀ {K : Type} [Field K] {T : TensorObj K 3} {t : ℕ} (G : T.TypeGrading t)
    (S : Finset (Fin t × Fin t × Fin t)) (_hSym : LaserSymmetric S)
    (_hsupport : TensorObj.LaserAlignedSupport G S) (π : (Fin t × Fin t × Fin t) → ℝ)
    (_hπ_supp : ∀ σ, σ ∉ S → π σ = 0) (_hπ_nn : ∀ σ, 0 ≤ π σ)
    (_hπ_sum : (∑ σ ∈ S, π σ) = 1),
    Real.exp (Real.log 2 * ( (-(∑ σ ∈ S, π σ * (Real.log (π σ) / Real.log 2))) +
      (1 / 3) * (∑ σ ∈ S, π σ * (Real.log (((Module.finrank K (G.classOf 0 σ.1) : ℕ) : ℝ) *
        ((Module.finrank K (G.classOf 1 σ.2.1) : ℕ) : ℝ) *
        ((Module.finrank K (G.classOf 2 σ.2.2) : ℕ) : ℝ)) / Real.log 2)) ) )
      ≤ subrankCapacityPoly T) := by
  intro h
  have hSym : LaserSymmetric ({((0 : Fin 1), (0 : Fin 1), (0 : Fin 1))} :
      Finset (Fin 1 × Fin 1 × Fin 1)) :=
    fun x _ => Finset.mem_singleton.mpr (Subsingleton.elim _ _)
  have hsupport : TensorObj.LaserAlignedSupport (lwd_trivialGrading ℚ)
      ({((0 : Fin 1), (0 : Fin 1), (0 : Fin 1))} : Finset (Fin 1 × Fin 1 × Fin 1)) :=
    ⟨0, fun j => Fin.elim0 j, fun j => Fin.elim0 j,
      by simp only [Finset.univ_eq_empty, Finset.sum_empty]; rfl,
      fun j => Fin.elim0 j⟩
  have hmain := @h ℚ _ TensorObj.zeroObj 1 (lwd_trivialGrading ℚ) {((0 : Fin 1), (0 : Fin 1), (0 : Fin 1))}
    hSym hsupport (fun _ => 1)
    (fun σ hσ => absurd (Finset.mem_singleton.mpr (Subsingleton.elim _ _)) hσ)
    (fun _ => zero_le_one) (by simp)
  rw [lwd_subrankCapacityPoly_zeroObj] at hmain
  exact absurd hmain (not_le.mpr (Real.exp_pos _))
