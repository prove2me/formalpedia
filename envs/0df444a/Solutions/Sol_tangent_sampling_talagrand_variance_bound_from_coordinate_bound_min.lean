-- Prove2me | solution 1 for tangent_sampling_talagrand_variance_bound_from_coordinate_bound_min
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-06-23T02:03:00.61516+00:00
-- url     : https://prove2.me/submissions/5dcb3241-0fc4-47e8-a5de-21b74e048c2b

import Definitions.Def_matrix_completion_talagrand
import Definitions.Def_tangent_projection_algebra
import Mathlib.Analysis.MeanInequalities
import Mathlib.Tactic

open MatrixCompletion
open scoped BigOperators

namespace MatrixCompletion

-- Reuse the CS lemma (copy of abs_matrixInner_le, proved in Scratch_min_increment)
lemma abs_matrixInner_le' {n1 n2 : Nat} (X Y : RealMatrix n1 n2) :
    |matrixInner X Y| ≤ frobeniusNorm X * frobeniusNorm Y := by
  have hCS :
      (matrixInner X Y) ^ 2 ≤ frobeniusNormSq X * frobeniusNormSq Y := by
    have flat : ∀ (F : Fin n1 → Fin n2 → ℝ),
        (∑ i : Fin n1, ∑ j : Fin n2, F i j) =
          ∑ p : Fin n1 × Fin n2, F p.1 p.2 := by
      intro F; rw [← Finset.sum_product']; rfl
    have key :
        (∑ p : Fin n1 × Fin n2, X p.1 p.2 * Y p.1 p.2) ^ 2 ≤
          (∑ p : Fin n1 × Fin n2, (X p.1 p.2) ^ 2) *
            (∑ p : Fin n1 × Fin n2, (Y p.1 p.2) ^ 2) :=
      Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
        (fun p : Fin n1 × Fin n2 => X p.1 p.2)
        (fun p : Fin n1 × Fin n2 => Y p.1 p.2)
    rw [matrixInner, frobeniusNormSq, frobeniusNormSq, flat, flat, flat]; exact key
  have hX : (0:ℝ) ≤ frobeniusNormSq X := by unfold frobeniusNormSq; positivity
  have hY : (0:ℝ) ≤ frobeniusNormSq Y := by unfold frobeniusNormSq; positivity
  have h1 : |matrixInner X Y| ≤ Real.sqrt (frobeniusNormSq X * frobeniusNormSq Y) := by
    rw [← Real.sqrt_sq_eq_abs]; apply Real.sqrt_le_sqrt; exact hCS
  calc |matrixInner X Y| ≤ Real.sqrt (frobeniusNormSq X * frobeniusNormSq Y) := h1
    _ = frobeniusNorm X * frobeniusNorm Y := by rw [Real.sqrt_mul hX]; rfl

/-- `⟨A, e_i e_j^*⟩ = A i j`. -/
lemma inner_coordinateMatrix {n1 n2 : Nat} (A : RealMatrix n1 n2)
    (i : Fin n1) (j : Fin n2) :
    matrixInner A (coordinateMatrix i j) = A i j := by
  unfold matrixInner coordinateMatrix
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb; simp [hb]
    · intro h; exact absurd (Finset.mem_univ j) h
  · intro a _ ha
    apply Finset.sum_eq_zero
    intro b _; simp [ha]
  · intro h; exact absurd (Finset.mem_univ i) h

/-- `matrixInner` is symmetric. -/
lemma matrixInner_comm {n1 n2 : Nat} (A B : RealMatrix n1 n2) :
    matrixInner A B = matrixInner B A := by
  unfold matrixInner
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  ring

/-- `matrixInner X X = frobeniusNorm X ^ 2`. -/
lemma matrixInner_self {n1 n2 : Nat} (X : RealMatrix n1 n2) :
    matrixInner X X = frobeniusNorm X ^ 2 := by
  unfold matrixInner frobeniusNorm frobeniusNormSq
  rw [Real.sq_sqrt]
  · apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _; ring
  · positivity

/-- BESSEL STEP: `∑_{ij} ⟨X, P_T(e_i e_j^*)⟩² = ‖P_T X‖_F² ≤ ‖X‖_F²`. -/
lemma sum_sq_inner_tangentCoord_le {n1 n2 r : Nat} {M : RealMatrix n1 n2}
    (S : SVD M r) (X : RealMatrix n1 n2) :
    ∑ i : Fin n1, ∑ j : Fin n2,
        (matrixInner X (tangentProjection S (coordinateMatrix i j))) ^ 2
      ≤ frobeniusNorm X ^ 2 := by
  -- ⟨X, P_T(e_ij)⟩ = ⟨P_T X, e_ij⟩ = (P_T X) i j
  have hcoord : ∀ i j,
      matrixInner X (tangentProjection S (coordinateMatrix i j))
        = (tangentProjection S X) i j := by
    intro i j
    rw [matrixInner_comm, TangentAlgebra.tangent_selfadjoint, matrixInner_comm,
        inner_coordinateMatrix]
  -- so the sum is ‖P_T X‖_F²
  have hsum :
      (∑ i : Fin n1, ∑ j : Fin n2,
        (matrixInner X (tangentProjection S (coordinateMatrix i j))) ^ 2)
        = frobeniusNorm (tangentProjection S X) ^ 2 := by
    have : (∑ i : Fin n1, ∑ j : Fin n2,
        (matrixInner X (tangentProjection S (coordinateMatrix i j))) ^ 2)
        = ∑ i : Fin n1, ∑ j : Fin n2, (tangentProjection S X) i j ^ 2 := by
      apply Finset.sum_congr rfl; intro i _
      apply Finset.sum_congr rfl; intro j _
      rw [hcoord]
    rw [this, ← matrixInner_self]; unfold matrixInner
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _; ring
  rw [hsum]
  -- ‖P_T X‖² = ⟨P_T X, P_T X⟩ = ⟨X, P_T (P_T X)⟩ = ⟨X, P_T X⟩ ≤ ‖X‖‖P_T X‖
  set PX := tangentProjection S X with hPX
  have hself : matrixInner PX PX = matrixInner X PX := by
    rw [hPX]
    rw [show matrixInner (tangentProjection S X) (tangentProjection S X)
          = matrixInner X (tangentProjection S (tangentProjection S X)) from
        TangentAlgebra.tangent_selfadjoint S X (tangentProjection S X)]
    rw [TangentAlgebra.tangent_idem]
  have hPXsq : frobeniusNorm PX ^ 2 = matrixInner X PX := by
    rw [← matrixInner_self, hself]
  -- ⟨X, PX⟩ ≤ ‖X‖ ‖PX‖
  have hCS : matrixInner X PX ≤ frobeniusNorm X * frobeniusNorm PX := by
    calc matrixInner X PX ≤ |matrixInner X PX| := le_abs_self _
      _ ≤ frobeniusNorm X * frobeniusNorm PX := abs_matrixInner_le' X PX
  have hPXnn : 0 ≤ frobeniusNorm PX := by unfold frobeniusNorm; positivity
  have hXnn : 0 ≤ frobeniusNorm X := by unfold frobeniusNorm; positivity
  -- ‖PX‖² ≤ ‖X‖‖PX‖ ⟹ ‖PX‖ ≤ ‖X‖ ⟹ ‖PX‖² ≤ ‖X‖²
  have hle : frobeniusNorm PX ^ 2 ≤ frobeniusNorm X * frobeniusNorm PX := by
    rw [hPXsq]; exact hCS
  rcases eq_or_lt_of_le hPXnn with hz | hpos
  · rw [← hz]; simp; positivity
  · have : frobeniusNorm PX ≤ frobeniusNorm X := by
      have h2 : frobeniusNorm PX * frobeniusNorm PX ≤ frobeniusNorm X * frobeniusNorm PX := by
        nlinarith [hle]
      exact le_of_mul_le_mul_right h2 hpos
    nlinarith [this, hPXnn, hXnn]

end MatrixCompletion

open MatrixCompletion

/-- Dimension-correct (`min`-radius) variance feed. -/
theorem solution :
    ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
      (μ₀ : ℝ) (S : SVD M r),
      0 < n₁ → 0 < n₂ → 0 < r → 0 < m → m ≤ n₁ * n₂ →
      1 ≤ μ₀ →
      TangentCoordinateFrobeniusBound S
        (2 * μ₀ * (r : ℝ) / (min n₁ n₂ : ℝ)) →
      TangentSamplingTalagrandVarianceBound S
        ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
        (2 * μ₀ * (↑(max n₁ n₂)) * (r : ℝ) / (m : ℝ)) := by
  intro n₁ n₂ r m M μ₀ S hn1 hn2 hr hm hmle hμ hcoord
  intro X1 X2 hX1 hX2
  set p : ℝ := (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)) with hpdef
  have hn1R : (0:ℝ) < n₁ := by exact_mod_cast hn1
  have hn2R : (0:ℝ) < n₂ := by exact_mod_cast hn2
  have hmR : (0:ℝ) < m := by exact_mod_cast hm
  have hprod : (0:ℝ) < (n₁ : ℝ) * (n₂ : ℝ) := mul_pos hn1R hn2R
  have hp_pos : 0 < p := by rw [hpdef]; positivity
  have hmleR : (m : ℝ) ≤ (n₁ : ℝ) * (n₂ : ℝ) := by exact_mod_cast hmle
  have hp_le1 : p ≤ 1 := by rw [hpdef]; rw [div_le_one hprod]; exact hmleR
  have hpinv_nonneg : 0 ≤ p⁻¹ := le_of_lt (inv_pos.mpr hp_pos)
  set Rmin : ℝ := 2 * μ₀ * (r : ℝ) / (min (n₁:ℝ) (n₂:ℝ)) with hRmin
  have hmin_pos : (0:ℝ) < min (n₁ : ℝ) (n₂ : ℝ) := lt_min hn1R hn2R
  have hμpos : 0 < μ₀ := lt_of_lt_of_le one_pos hμ
  have hRmin_nonneg : 0 ≤ Rmin := by rw [hRmin]; positivity
  -- termwise bound: p(1-p)·coeff² ≤ p⁻¹ · Rmin · ⟨X1,P_ij⟩²
  have hX2norm : frobeniusNorm X2 ≤ 1 := hX2
  have hterm : ∀ i j,
      p * (1 - p) * (tangentSamplingTalagrandCoefficient S p X1 X2 i j) ^ 2
        ≤ p⁻¹ * Rmin *
            (matrixInner X1 (tangentProjection S (coordinateMatrix i j))) ^ 2 := by
    intro i j
    set P := tangentProjection S (coordinateMatrix i j) with hP
    have hPnn : 0 ≤ frobeniusNorm P := by unfold frobeniusNorm; positivity
    -- ⟨P,X2⟩² ≤ ‖P‖² ≤ Rmin
    have h1 : |matrixInner P X2| ≤ frobeniusNorm P := by
      calc |matrixInner P X2| ≤ frobeniusNorm P * frobeniusNorm X2 :=
            abs_matrixInner_le' P X2
        _ ≤ frobeniusNorm P * 1 := by
              apply mul_le_mul_of_nonneg_left hX2norm hPnn
        _ = frobeniusNorm P := mul_one _
    have hPX2 : (matrixInner P X2) ^ 2 ≤ frobeniusNorm P ^ 2 := by
      have habs := abs_nonneg (matrixInner P X2)
      have hsqabs : (matrixInner P X2) ^ 2 = |matrixInner P X2| ^ 2 := (sq_abs _).symm
      rw [hsqabs]
      nlinarith [h1, habs, hPnn]
    have hPsq : frobeniusNorm P ^ 2 ≤ Rmin := hcoord i j
    have hPX2_le : (matrixInner P X2) ^ 2 ≤ Rmin := le_trans hPX2 hPsq
    -- coeff² = p⁻²·⟨X1,P⟩²·⟨P,X2⟩²
    have hcoeff_sq :
        (tangentSamplingTalagrandCoefficient S p X1 X2 i j) ^ 2
          = (p⁻¹) ^ 2 * (matrixInner X1 P) ^ 2 * (matrixInner P X2) ^ 2 := by
      unfold tangentSamplingTalagrandCoefficient; rw [← hP]; ring
    rw [hcoeff_sq]
    -- p(1-p)·p⁻²·A·B  with A=⟨X1,P⟩²≥0, B=⟨P,X2⟩²≤Rmin
    have hA_nn : 0 ≤ (matrixInner X1 P) ^ 2 := sq_nonneg _
    have hB_nn : 0 ≤ (matrixInner P X2) ^ 2 := sq_nonneg _
    -- p(1-p)p⁻² = (1-p)/p ≤ p⁻¹  (since 1-p ≤ 1, p>0)
    have hfac : p * (1 - p) * (p⁻¹) ^ 2 ≤ p⁻¹ := by
      have hpne : p ≠ 0 := ne_of_gt hp_pos
      rw [show p * (1 - p) * (p⁻¹) ^ 2 = (1 - p) * p⁻¹ from by
        field_simp]
      have h1p : 1 - p ≤ 1 := by linarith
      calc (1 - p) * p⁻¹ ≤ 1 * p⁻¹ := by
            apply mul_le_mul_of_nonneg_right h1p hpinv_nonneg
        _ = p⁻¹ := one_mul _
    -- assemble
    calc p * (1 - p) * ((p⁻¹) ^ 2 * (matrixInner X1 P) ^ 2 * (matrixInner P X2) ^ 2)
          = (p * (1 - p) * (p⁻¹) ^ 2) * (matrixInner X1 P) ^ 2 * (matrixInner P X2) ^ 2 := by ring
      _ ≤ p⁻¹ * (matrixInner X1 P) ^ 2 * (matrixInner P X2) ^ 2 := by
            apply mul_le_mul_of_nonneg_right _ hB_nn
            apply mul_le_mul_of_nonneg_right hfac hA_nn
      _ ≤ p⁻¹ * (matrixInner X1 P) ^ 2 * Rmin := by
            apply mul_le_mul_of_nonneg_left hPX2_le
            apply mul_nonneg hpinv_nonneg hA_nn
      _ = p⁻¹ * Rmin * (matrixInner X1 P) ^ 2 := by ring
  -- sum the termwise bound
  calc ∑ i : Fin n₁, ∑ j : Fin n₂,
        p * (1 - p) * (tangentSamplingTalagrandCoefficient S p X1 X2 i j) ^ 2
      ≤ ∑ i : Fin n₁, ∑ j : Fin n₂,
          p⁻¹ * Rmin *
            (matrixInner X1 (tangentProjection S (coordinateMatrix i j))) ^ 2 := by
        apply Finset.sum_le_sum; intro i _
        apply Finset.sum_le_sum; intro j _
        exact hterm i j
    _ = p⁻¹ * Rmin *
          ∑ i : Fin n₁, ∑ j : Fin n₂,
            (matrixInner X1 (tangentProjection S (coordinateMatrix i j))) ^ 2 := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; rw [Finset.mul_sum]
    _ ≤ p⁻¹ * Rmin * (frobeniusNorm X1 ^ 2) := by
        apply mul_le_mul_of_nonneg_left (sum_sq_inner_tangentCoord_le S X1)
        exact mul_nonneg hpinv_nonneg hRmin_nonneg
    _ ≤ p⁻¹ * Rmin * 1 := by
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg hpinv_nonneg hRmin_nonneg)
        have hX1norm : frobeniusNorm X1 ≤ 1 := hX1
        have hX1nn : 0 ≤ frobeniusNorm X1 := by unfold frobeniusNorm; positivity
        nlinarith [hX1norm, hX1nn]
    _ = 2 * μ₀ * (↑(max n₁ n₂)) * (r : ℝ) / (m : ℝ) := by
        rw [mul_one, hRmin, hpdef]
        rw [inv_div]
        have hmax_cast : ((max n₁ n₂ : ℕ) : ℝ) = max (n₁ : ℝ) (n₂ : ℝ) := by push_cast; rfl
        rw [hmax_cast]
        have hmm : ((n₁:ℝ) * (n₂:ℝ)) / (min (n₁:ℝ) (n₂:ℝ)) = max (n₁:ℝ) (n₂:ℝ) := by
          rcases le_total (n₁:ℝ) (n₂:ℝ) with h | h
          · rw [min_eq_left h, max_eq_right h]
            have : (n₁:ℝ) ≠ 0 := ne_of_gt hn1R; field_simp
          · rw [min_eq_right h, max_eq_left h]
            have : (n₂:ℝ) ≠ 0 := ne_of_gt hn2R; field_simp
        have hmin_ne : min (n₁:ℝ) (n₂:ℝ) ≠ 0 := ne_of_gt hmin_pos
        have hm_ne : (m:ℝ) ≠ 0 := ne_of_gt hmR
        field_simp
        have hmm' : (n₁:ℝ) * (n₂:ℝ) = max (n₁:ℝ) (n₂:ℝ) * min (n₁:ℝ) (n₂:ℝ) := by
          rw [← hmm]; field_simp
        nlinarith [hmm', hmin_pos, hmR]
