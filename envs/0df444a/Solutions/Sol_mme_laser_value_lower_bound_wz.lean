-- Prove2me | solution 1 for mme_laser_value_lower_bound_wz
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-06T12:15:50.460525+00:00
-- url     : https://prove2.me/submissions/52c50f1a-3e88-4ba5-b5c7-e435eb19f52c

import Definitions.Def_mme_laser_value_formula_wz
import Definitions.Def_mme_laser_pattern
import Definitions.Def_mme_subrank_capacity
open MME

set_option autoImplicit false

open PiTensorProduct in
/-- The matrix-multiplication tensor `⟨a,b,c⟩` is nonzero whenever `a, b, c ≥ 1`:
the coordinate functional at the entries `(0,0)`, `(0,0)`, `(0,0)` evaluates to `1`. -/
theorem MMTensor_ne_zero_aux {K : Type} [Field K] (a b c : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    MMTensor K a b c ≠ 0 := by
  let i0 : Fin a := ⟨0, ha⟩
  let j0 : Fin b := ⟨0, hb⟩
  let k0 : Fin c := ⟨0, hc⟩
  let ev : ∀ i : Fin 3, MMSpace K a b c i →ₗ[K] K := fun i =>
    match i with
    | ⟨0, _⟩ => LinearMap.proj (i0, j0)
    | ⟨1, _⟩ => LinearMap.proj (j0, k0)
    | ⟨2, _⟩ => LinearMap.proj (k0, i0)
  let φ : PiTensorProduct K (MMSpace K a b c) →ₗ[K] K :=
    PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra K (Fin 3) K).compLinearMap ev)
  intro h
  have key : φ (MMTensor K a b c) = 1 := by
    simp only [MMTensor, map_sum, φ, PiTensorProduct.lift.tprod,
      MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply, Fin.prod_univ_three]
    simp only [ev, LinearMap.proj_apply, Pi.single_apply]
    rw [Fintype.sum_eq_single i0, Fintype.sum_eq_single j0, Fintype.sum_eq_single k0]
    · simp
    · intro z hz; simp [Ne.symm hz]
    · intro y hy; exact Finset.sum_eq_zero fun z _ => by simp [Ne.symm hy]
    · intro x hx
      exact Finset.sum_eq_zero fun y _ => Finset.sum_eq_zero fun z _ => by simp [Ne.symm hx]
  rw [h, map_zero] at key
  exact zero_ne_one key

/-- If one component `a b c` is not all positive, the product `a * b * c` vanishes. -/
theorem MMTensor_eq_zero_imp {K : Type} [Field K] (a b c : ℕ) (h : MMTensor K a b c = 0) :
    a * b * c = 0 := by
  by_contra hne
  have ha : 0 < a := Nat.pos_of_ne_zero (fun h0 => hne (by simp [h0]))
  have hb : 0 < b := Nat.pos_of_ne_zero (fun h0 => hne (by simp [h0]))
  have hc : 0 < c := Nat.pos_of_ne_zero (fun h0 => hne (by simp [h0]))
  exact MMTensor_ne_zero_aux a b c ha hb hc h

open PiTensorProduct in
/-- `PiTensorProduct.map` of the zero family is zero (for a nonempty index type). -/
theorem piTensor_map_zero_family {K : Type} [Field K] {d : ℕ} (hd : 0 < d)
    {V W : Fin d → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)] :
    PiTensorProduct.map (fun i => (0 : V i →ₗ[K] W i)) = 0 := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro v
  simp only [LinearMap.compMultilinearMap_apply, PiTensorProduct.map_tprod, LinearMap.zero_apply]
  exact (PiTensorProduct.tprod K).map_coord_zero ⟨0, hd⟩ rfl

open PiTensorProduct in
/-- If the direct sum of two tensor objects has zero tensor, both summands do. -/
theorem add_t_eq_zero {K : Type} [Field K] {d : ℕ} (hd : 0 < d) (X Y : TensorObj K d)
    (h : (TensorObj.add X Y).t = 0) : X.t = 0 ∧ Y.t = 0 := by
  have h' : PiTensorProduct.map (fun i => LinearMap.inl K (X.V i) (Y.V i)) X.t
      + PiTensorProduct.map (fun i => LinearMap.inr K (X.V i) (Y.V i)) Y.t
      = (0 : PiTensorProduct K fun i => X.V i × Y.V i) := h
  have e1 : PiTensorProduct.map (fun i => LinearMap.fst K (X.V i) (Y.V i)) ∘ₗ
      PiTensorProduct.map (fun i => LinearMap.inl K (X.V i) (Y.V i)) = LinearMap.id := by
    rw [← PiTensorProduct.map_comp]
    simp only [LinearMap.fst_comp_inl]
    exact PiTensorProduct.map_id
  have e2 : PiTensorProduct.map (fun i => LinearMap.fst K (X.V i) (Y.V i)) ∘ₗ
      PiTensorProduct.map (fun i => LinearMap.inr K (X.V i) (Y.V i)) = 0 := by
    rw [← PiTensorProduct.map_comp]
    simp only [LinearMap.fst_comp_inr]
    exact piTensor_map_zero_family hd
  have e3 : PiTensorProduct.map (fun i => LinearMap.snd K (X.V i) (Y.V i)) ∘ₗ
      PiTensorProduct.map (fun i => LinearMap.inl K (X.V i) (Y.V i)) = 0 := by
    rw [← PiTensorProduct.map_comp]
    simp only [LinearMap.snd_comp_inl]
    exact piTensor_map_zero_family hd
  have e4 : PiTensorProduct.map (fun i => LinearMap.snd K (X.V i) (Y.V i)) ∘ₗ
      PiTensorProduct.map (fun i => LinearMap.inr K (X.V i) (Y.V i)) = LinearMap.id := by
    rw [← PiTensorProduct.map_comp]
    simp only [LinearMap.snd_comp_inr]
    exact PiTensorProduct.map_id
  constructor
  · have := congrArg (PiTensorProduct.map (fun i => LinearMap.fst K (X.V i) (Y.V i))) h'
    rw [map_add, map_zero] at this
    have e1' := LinearMap.congr_fun e1 X.t
    have e2' := LinearMap.congr_fun e2 Y.t
    simp only [LinearMap.comp_apply, LinearMap.id_apply, LinearMap.zero_apply] at e1' e2'
    rw [e1', e2', add_zero] at this
    exact this
  · have := congrArg (PiTensorProduct.map (fun i => LinearMap.snd K (X.V i) (Y.V i))) h'
    rw [map_add, map_zero] at this
    have e3' := LinearMap.congr_fun e3 X.t
    have e4' := LinearMap.congr_fun e4 Y.t
    simp only [LinearMap.comp_apply, LinearMap.id_apply, LinearMap.zero_apply] at e3' e4'
    rw [e3', e4', zero_add] at this
    exact this

/-- If a finite direct sum has zero tensor, every summand does. -/
theorem bigAdd_components_zero {K : Type} [Field K] {d : ℕ} (hd : 0 < d) :
    ∀ {k : ℕ} (f : Fin k → TensorObj K d), (TensorObj.bigAdd f).t = 0 → ∀ i, (f i).t = 0
  | 0, _, _, i => i.elim0
  | 1, f, h, i => by
      have hi : i = 0 := Subsingleton.elim _ _
      subst hi
      exact h
  | k + 2, f, h, i => by
      rw [TensorObj.bigAdd] at h
      obtain ⟨h0, h1⟩ := add_t_eq_zero hd _ _ h
      refine Fin.cases h0 (fun j => ?_) i
      exact bigAdd_components_zero hd (fun i => f i.succ) h1 j

/-- The zero tensor with three one-dimensional mode spaces. -/
noncomputable def ZeroT : TensorObj ℚ 3 := { V := fun _ => ℚ, t := 0 }

/-- The trivial one-class grading of `ZeroT`. -/
noncomputable def ZeroG : ZeroT.TypeGrading 1 where
  decomp := fun _ _ => ⊤
  is_internal := fun _ => by
    apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    · exact iSupIndep_subsingleton _
    · simp

/-- The single-triple support pattern. -/
def S0 : Finset (Fin 1 × Fin 1 × Fin 1) := {((0 : Fin 1), (0 : Fin 1), (0 : Fin 1))}

theorem mem_S0 (x : Fin 1 × Fin 1 × Fin 1) : x ∈ S0 :=
  Finset.mem_singleton.mpr (Subsingleton.elim _ _)

theorem ZeroT_kronPow_succ (N : ℕ) : (ZeroT.kronPow (N + 1)).t = 0 := by
  show interchange ZeroT.t (ZeroT.kronPow N).t = 0
  rw [show ZeroT.t = 0 from rfl, map_zero, LinearMap.zero_apply]

theorem finrank_ZeroG (i : Fin 3) (α : Fin 1) :
    Module.finrank ℚ (ZeroG.classOf i α : Submodule ℚ (ZeroT.V i)) = 1 :=
  (finrank_top ℚ ℚ).trans (Module.finrank_self ℚ)

theorem laser_ZeroG : laserValueFormula_wz ZeroG S0 = 1 := by
  unfold laserValueFormula_wz
  have hset : { v : ℝ |
    ∃ π : (Fin 1 × Fin 1 × Fin 1) → ℝ,
      (∀ σ, σ ∉ S0 → π σ = 0) ∧
      (∀ σ, 0 ≤ π σ) ∧
      (∑ σ ∈ S0, π σ) = 1 ∧
      v = Real.exp (Real.log 2 *
        ( (-(∑ σ ∈ S0, π σ * (Real.log (π σ) / Real.log 2)))
        + (1 / 3) *
            (∑ σ ∈ S0, π σ *
              (Real.log
                  (((Module.finrank ℚ (ZeroG.classOf 0 σ.1) : ℕ) : ℝ) *
                   ((Module.finrank ℚ (ZeroG.classOf 1 σ.2.1) : ℕ) : ℝ) *
                   ((Module.finrank ℚ (ZeroG.classOf 2 σ.2.2) : ℕ) : ℝ))
                / Real.log 2)) ) ) } = {1} := by
    ext v
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, S0, Finset.sum_singleton, finrank_ZeroG]
    constructor
    · rintro ⟨π, -, -, hsum, rfl⟩
      simp [hsum]
    · rintro rfl
      refine ⟨fun _ => 1, fun σ hσ => absurd (mem_S0 σ) (by simpa [S0] using hσ),
        fun _ => zero_le_one, rfl, ?_⟩
      simp
  rw [hset, csSup_singleton]

theorem subrank_ZeroT : subrankCapacity ZeroT = 0 := by
  unfold subrankCapacity
  have hset : { V : ℝ | 1 ≤ V ∧
    ∀ ε > (0 : ℝ), ∃ᶠ N in Filter.atTop,
      ∃ (k : ℕ) (a b c : Fin k → ℕ),
        TensorObj.Restrict
          (TensorObj.bigAdd (fun i => MMObj ℚ (a i) (b i) (c i)))
          (ZeroT.kronPow N)
        ∧ V ^ N * (1 - ε) ≤ ∑ i, ((a i * b i * c i : ℕ) : ℝ) ^ ((1 : ℝ) / 3) } = ∅ := by
    ext V
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
    intro hV hfreq
    obtain ⟨N, hN, k, a, b, c, ⟨f, hf⟩, hle⟩ := Filter.frequently_atTop.mp (hfreq (1/2) (by norm_num)) 1
    obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
    rw [ZeroT_kronPow_succ, map_zero] at hf
    have hzero : ∀ i, a i * b i * c i = 0 := fun i =>
      MMTensor_eq_zero_imp (a i) (b i) (c i)
        (bigAdd_components_zero (by norm_num) (fun i => MMObj ℚ (a i) (b i) (c i)) hf.symm i)
    have hsum : ∑ i, ((a i * b i * c i : ℕ) : ℝ) ^ ((1 : ℝ) / 3) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      rw [hzero i]
      simp
    rw [hsum] at hle
    have hpos : 0 < V ^ (M + 1) * (1 - 1 / 2) := by
      have : (1 : ℝ) ≤ V ^ (M + 1) := one_le_pow₀ hV
      nlinarith
    linarith
  rw [hset, Real.sSup_empty]

theorem solution : ¬ (∀ {K : Type} [Field K] {T : TensorObj K 3} {t : ℕ} (G : T.TypeGrading t)
    (S : Finset (Fin t × Fin t × Fin t)) (_hSym : LaserSymmetric S)
    (_hsupport : TensorObj.LaserAlignedSupport G S),
    laserValueFormula_wz G S ≤ subrankCapacity T) := by
  intro h
  have hSym : LaserSymmetric S0 := fun x _ => mem_S0 _
  have hsupport : TensorObj.LaserAlignedSupport ZeroG S0 :=
    ⟨0, Fin.elim0, Fin.elim0, (Fin.sum_univ_zero _).symm, fun j => j.elim0⟩
  have := h ZeroG S0 hSym hsupport
  rw [laser_ZeroG, subrank_ZeroT] at this
  exact absurd this (by norm_num)
