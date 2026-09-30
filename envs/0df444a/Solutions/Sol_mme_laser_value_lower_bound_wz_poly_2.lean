-- Prove2me | solution 2 for mme_laser_value_lower_bound_wz_poly
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-06T13:57:26.1639+00:00
-- url     : https://prove2.me/submissions/7ff7ea23-b91b-43d4-9ba8-9ca0073a0080

import Definitions.Def_mme_laser_value_formula_wz
import Definitions.Def_mme_laser_pattern
import Definitions.Def_mme_subrank_capacity_poly
open MME

/-!
Disproof of `mme_laser_value_lower_bound_wz_poly`.

Counterexample: the zero tensor `Z0 : TensorObj ℚ 3` with all three mode spaces equal
to `ℚ`, the trivial `1`-grading `G0` (each class is `⊤`), and the full support
`S0 = univ : Finset (Fin 1 × Fin 1 × Fin 1)`.

* `LaserSymmetric S0` is trivial and `LaserAlignedSupport G0 S0` holds with the empty
  rank-one expansion (`Z0.t = 0 = ∑ over Fin 0`).
* `laserValueFormula_wz G0 S0 = 1` (the only probability distribution on `S0` is the
  point mass, and every grading class is one-dimensional).
* `subrankCapacityPoly Z0 = sSup ∅ = 0`: for `N ≥ 1` the Kronecker power `Z0^N` has
  zero tensor, so any restriction of a direct sum of `MMObj`'s forces every summand to
  have `a·b·c = 0`, and the required inequality `V^N (1-ε) ≤ 0` fails for `V ≥ 1`.
-/

open PiTensorProduct BigOperators Filter

/-- The zero tensor with three copies of `ℚ` as mode spaces. -/
noncomputable def Z0 : TensorObj ℚ 3 where
  V _ := ℚ
  t := 0

/-- The trivial `1`-grading of `Z0`: the unique class of every mode is `⊤`. -/
noncomputable def G0 : Z0.TypeGrading 1 where
  decomp _ _ := ⊤
  is_internal i := by
    rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
    exact ⟨iSupIndep_subsingleton _, by simp⟩

/-- The full support pattern on `Fin 1 × Fin 1 × Fin 1`. -/
def S0 : Finset (Fin 1 × Fin 1 × Fin 1) := Finset.univ

lemma S0_sym : LaserSymmetric S0 := fun _ _ => Finset.mem_univ _

lemma S0_support : TensorObj.LaserAlignedSupport G0 S0 :=
  ⟨0, Fin.elim0, Fin.elim0, by
    show (0 : PiTensorProduct ℚ Z0.V) = ∑ j : Fin 0, PiTensorProduct.tprod ℚ (Fin.elim0 j)
    rw [Finset.univ_eq_empty, Finset.sum_empty], fun j => j.elim0⟩

lemma finrank_class (i : Fin 3) (α : Fin 1) :
    Module.finrank ℚ (G0.classOf i α) = 1 := by
  show Module.finrank ℚ (⊤ : Submodule ℚ ℚ) = 1
  rw [finrank_top, Module.finrank_self]

lemma sum_S0 (f : Fin 1 × Fin 1 × Fin 1 → ℝ) : ∑ σ ∈ S0, f σ = f (0, 0, 0) := by
  simp [S0, Fintype.sum_prod_type]

/-- Every member of the defining set of `laserValueFormula_wz G0 S0` equals `1`. -/
lemma value_eq_one (π : (Fin 1 × Fin 1 × Fin 1) → ℝ) (hsum : (∑ σ ∈ S0, π σ) = 1) :
    Real.exp (Real.log 2 *
        ( (-(∑ σ ∈ S0, π σ * (Real.log (π σ) / Real.log 2)))
        + (1 / 3) *
            (∑ σ ∈ S0, π σ *
              (Real.log
                  (((Module.finrank ℚ (G0.classOf 0 σ.1) : ℕ) : ℝ) *
                   ((Module.finrank ℚ (G0.classOf 1 σ.2.1) : ℕ) : ℝ) *
                   ((Module.finrank ℚ (G0.classOf 2 σ.2.2) : ℕ) : ℝ))
                / Real.log 2)) ) ) = 1 := by
  rw [sum_S0] at hsum
  rw [sum_S0, sum_S0, hsum]
  simp [finrank_class]

lemma lvf_ge_one : (1 : ℝ) ≤ laserValueFormula_wz G0 S0 := by
  unfold laserValueFormula_wz
  apply le_csSup
  · refine ⟨1, ?_⟩
    rintro v ⟨π, -, -, hsum, rfl⟩
    exact (value_eq_one π hsum).le
  · refine ⟨fun _ => 1, fun σ h => absurd (Finset.mem_univ σ) h, fun _ => zero_le_one, ?_, ?_⟩
    · rw [sum_S0]
    · symm
      apply value_eq_one
      rw [sum_S0]

/-! ### A "mass" functional on direct sums of matrix-multiplication tensors -/

/-- Sum-of-coordinates functionals on the three mode spaces of `MMObj ℚ n m p`. -/
noncomputable def sumFun (n m p : ℕ) : ∀ i : Fin 3, MMSpace ℚ n m p i →ₗ[ℚ] ℚ
  | ⟨0, _⟩ => ∑ x : Fin n × Fin m, LinearMap.proj x
  | ⟨1, _⟩ => ∑ x : Fin m × Fin p, LinearMap.proj x
  | ⟨2, _⟩ => ∑ x : Fin p × Fin n, LinearMap.proj x

/-- The rank-one factors of `MMTensor`. -/
noncomputable def mmVec (n m p : ℕ) (i : Fin n) (j : Fin m) (k : Fin p) :
    ∀ s : Fin 3, MMSpace ℚ n m p s
  | ⟨0, _⟩ => (Pi.single (i, j) 1 : Fin n × Fin m → ℚ)
  | ⟨1, _⟩ => (Pi.single (j, k) 1 : Fin m × Fin p → ℚ)
  | ⟨2, _⟩ => (Pi.single (k, i) 1 : Fin p × Fin n → ℚ)

lemma MMTensor_eq (n m p : ℕ) :
    MMTensor ℚ n m p = ∑ i : Fin n, ∑ j : Fin m, ∑ k : Fin p, PiTensorProduct.tprod ℚ (mmVec n m p i j k) := rfl

lemma sumFun_mmVec (n m p : ℕ) (i : Fin n) (j : Fin m) (k : Fin p) (s : Fin 3) :
    sumFun n m p s (mmVec n m p i j k s) = 1 := by
  fin_cases s <;> simp [sumFun, mmVec, LinearMap.sum_apply]

lemma mass_MM (n m p : ℕ) :
    ∃ φ : PiTensorProduct ℚ (MMObj ℚ n m p).V →ₗ[ℚ] ℚ,
      φ (MMObj ℚ n m p).t = ((n * m * p : ℕ) : ℚ) := by
  refine ⟨lift ((MultilinearMap.mkPiAlgebra ℚ (Fin 3) ℚ).compLinearMap (sumFun n m p)), ?_⟩
  show lift ((MultilinearMap.mkPiAlgebra ℚ (Fin 3) ℚ).compLinearMap (sumFun n m p))
      (MMTensor ℚ n m p) = ((n * m * p : ℕ) : ℚ)
  rw [MMTensor_eq]
  simp only [map_sum, lift.tprod, MultilinearMap.compLinearMap_apply,
    MultilinearMap.mkPiAlgebra_apply, sumFun_mmVec, Finset.prod_const_one, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin]
  push_cast
  ring

lemma mass_add {X Y : TensorObj ℚ 3} {a b : ℚ}
    (hX : ∃ φ : PiTensorProduct ℚ X.V →ₗ[ℚ] ℚ, φ X.t = a)
    (hY : ∃ φ : PiTensorProduct ℚ Y.V →ₗ[ℚ] ℚ, φ Y.t = b) :
    ∃ φ : PiTensorProduct ℚ (TensorObj.add X Y).V →ₗ[ℚ] ℚ,
      φ (TensorObj.add X Y).t = a + b := by
  obtain ⟨φX, hφX⟩ := hX
  obtain ⟨φY, hφY⟩ := hY
  let MX : MultilinearMap ℚ X.V ℚ := φX.compMultilinearMap (PiTensorProduct.tprod ℚ)
  let MY : MultilinearMap ℚ Y.V ℚ := φY.compMultilinearMap (PiTensorProduct.tprod ℚ)
  let M : MultilinearMap ℚ (fun i => X.V i × Y.V i) ℚ :=
    MX.compLinearMap (fun i => LinearMap.fst ℚ (X.V i) (Y.V i)) +
    MY.compLinearMap (fun i => LinearMap.snd ℚ (X.V i) (Y.V i))
  refine ⟨lift M, ?_⟩
  show lift M (PiTensorProduct.map (fun i => LinearMap.inl ℚ (X.V i) (Y.V i)) X.t +
       PiTensorProduct.map (fun i => LinearMap.inr ℚ (X.V i) (Y.V i)) Y.t) = a + b
  rw [map_add]
  have h1 : lift M (PiTensorProduct.map (fun i => LinearMap.inl ℚ (X.V i) (Y.V i)) X.t)
      = φX X.t := by
    rw [← LinearMap.comp_apply, lift_comp_map]
    congr 1
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro v
    have h0 : (PiTensorProduct.tprod ℚ) (fun i => (0 : Y.V i)) = 0 := MultilinearMap.map_zero _
    simp only [LinearMap.compMultilinearMap_apply, lift.tprod, MultilinearMap.compLinearMap_apply,
      add_apply, M, MX, MY, LinearMap.inl_apply, LinearMap.fst_apply,
      LinearMap.snd_apply, h0, map_zero, add_zero]
  have h2 : lift M (PiTensorProduct.map (fun i => LinearMap.inr ℚ (X.V i) (Y.V i)) Y.t)
      = φY Y.t := by
    rw [← LinearMap.comp_apply, lift_comp_map]
    congr 1
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro v
    have h0 : (PiTensorProduct.tprod ℚ) (fun i => (0 : X.V i)) = 0 := MultilinearMap.map_zero _
    simp only [LinearMap.compMultilinearMap_apply, lift.tprod, MultilinearMap.compLinearMap_apply,
      add_apply, M, MX, MY, LinearMap.inr_apply, LinearMap.fst_apply,
      LinearMap.snd_apply, h0, map_zero, zero_add]
  rw [h1, h2, hφX, hφY]

lemma mass_bigAdd : ∀ (k : ℕ) (f : Fin k → TensorObj ℚ 3) (m : Fin k → ℚ),
    (∀ i, ∃ φ : PiTensorProduct ℚ (f i).V →ₗ[ℚ] ℚ, φ (f i).t = m i) →
    ∃ φ : PiTensorProduct ℚ (TensorObj.bigAdd f).V →ₗ[ℚ] ℚ,
      φ (TensorObj.bigAdd f).t = ∑ i, m i
  | 0, _, m, _ => ⟨0, by rw [Finset.univ_eq_empty, Finset.sum_empty]; rfl⟩
  | 1, f, m, h => by
      obtain ⟨φ, hφ⟩ := h 0
      exact ⟨φ, by rw [Fin.sum_univ_one]; exact hφ⟩
  | (k+2), f, m, h => by
      have ih := mass_bigAdd (k+1) (fun i => f i.succ) (fun i => m i.succ) (fun i => h i.succ)
      have hadd := mass_add (h 0) ih
      rw [Fin.sum_univ_succ]
      exact hadd

lemma abc_zero (k : ℕ) (a b c : Fin k → ℕ)
    (h : (TensorObj.bigAdd (fun i => MMObj ℚ (a i) (b i) (c i))).t = 0) :
    ∀ i, a i * b i * c i = 0 := by
  obtain ⟨φ, hφ⟩ := mass_bigAdd k (fun i => MMObj ℚ (a i) (b i) (c i))
    (fun i => ((a i * b i * c i : ℕ) : ℚ)) (fun i => mass_MM (a i) (b i) (c i))
  rw [h, map_zero] at hφ
  have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Nat.cast_nonneg _)).mp hφ.symm
  intro i
  exact_mod_cast hz i (Finset.mem_univ i)

lemma kronPow_t_zero (N : ℕ) (hN : 1 ≤ N) : (Z0.kronPow N).t = 0 := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  show interchange Z0.t (Z0.kronPow n).t = 0
  rw [show Z0.t = 0 from rfl, map_zero, LinearMap.zero_apply]

lemma cap_zero : subrankCapacityPoly Z0 = 0 := by
  unfold subrankCapacityPoly
  convert Real.sSup_empty
  ext V
  simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and, not_exists]
  intro hV1 c hc
  obtain ⟨N, hN1, k, a, b, c', -, hres, hineq⟩ :=
    (Filter.frequently_atTop.mp (hc (1/2) (by norm_num))) 1
  obtain ⟨f, hf⟩ := hres
  rw [kronPow_t_zero N hN1, map_zero] at hf
  have hz := abc_zero k a b c' hf.symm
  have hsum : ∑ i, (((a i * b i * c' i : ℕ) : ℝ) ^ ((1 : ℝ) / 3)) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    rw [hz i]
    simp
  rw [hsum] at hineq
  have hpos : (0 : ℝ) < V ^ N * (1 - 1 / 2) := by
    have : (0 : ℝ) < V ^ N := pow_pos (by linarith) N
    linarith
  linarith

theorem solution : ¬ (∀ {K : Type} [Field K] {T : TensorObj K 3} {t : ℕ} (G : T.TypeGrading t)
    (S : Finset (Fin t × Fin t × Fin t)) (_hSym : LaserSymmetric S)
    (_hsupport : TensorObj.LaserAlignedSupport G S),
    laserValueFormula_wz G S ≤ subrankCapacityPoly T) := by
  intro h
  have := h G0 S0 S0_sym S0_support
  rw [cap_zero] at this
  linarith [lvf_ge_one]
