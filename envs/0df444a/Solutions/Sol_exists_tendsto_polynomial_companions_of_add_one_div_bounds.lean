-- Prove2me | solution 1 for exists_tendsto_polynomial_companions_of_add_one_div_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:51:40.149859+00:00
-- url     : https://prove2.me/submissions/6f5e1ba9-4c94-45af-ac83-b0fe3242d1d7

import Definitions.Def_Operator_Crouzeix_PolynomialSupNormZero
import Definitions.Def_Operator_Crouzeix_PolynomialCompanionNormalization
import Theorems.Thm_mem_numericalRange
import Theorems.Thm_polynomialSupNorm_smul
attribute [local simp] mem_numericalRange


section
open Filter
universe u
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E]
private theorem
    exists_tendsto_polynomial_companions_of_add_one_div_bounds_of_pos
    (A : E →L[ℂ] E) (S : Set ℂ) (m : ℝ) (hm : 0 < m)
    (G : E →L[ℂ] E) (r : ℕ → Polynomial ℂ)
    (hr : ∀ j, polynomialSupNorm (r j) S ≤
      m + 1 / ((j : ℝ) + 1))
    (hrlim : Tendsto (fun j ↦ Polynomial.aeval A (r j)) atTop (nhds G)) :
    ∃ q : ℕ → Polynomial ℂ,
      (∀ j, polynomialSupNorm (q j) S ≤ m) ∧
      Tendsto (fun j ↦ Polynomial.aeval A (q j)) atTop (nhds G) := by
  let ε : ℕ → ℝ := fun j ↦ 1 / ((j : ℝ) + 1)
  let a : ℕ → ℝ := fun j ↦ m / (m + ε j)
  let q : ℕ → Polynomial ℂ := fun j ↦ ((a j : ℝ) : ℂ) • r j
  refine ⟨q, ?_, ?_⟩
  · intro j
    have hε : 0 < ε j := by
      dsimp only [ε]
      positivity
    have hdenom : 0 < m + ε j := add_pos hm hε
    dsimp only [q]
    rw [polynomialSupNorm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (div_pos hm hdenom)]
    calc
      m / (m + ε j) * polynomialSupNorm (r j) S ≤
          m / (m + ε j) * (m + ε j) :=
        mul_le_mul_of_nonneg_left (by simpa only [ε] using hr j)
          (div_nonneg hm.le hdenom.le)
      _ = m := by field_simp
  · have hεlim : Tendsto ε atTop (nhds 0) := by
      simpa only [ε] using
        (tendsto_one_div_add_atTop_nhds_zero_nat :
          Tendsto (fun j : ℕ ↦ 1 / ((j : ℝ) + 1)) atTop (nhds 0))
    have halim : Tendsto a atTop (nhds 1) := by
      have hnum : Tendsto (fun _ : ℕ ↦ m) atTop (nhds m) :=
        tendsto_const_nhds
      have hden : Tendsto (fun j ↦ m + ε j) atTop (nhds (m + 0)) :=
        tendsto_const_nhds.add hεlim
      have hdiv := hnum.div hden (by simpa only [add_zero] using hm.ne')
      change Tendsto (fun j ↦ m / (m + ε j)) atTop (nhds 1)
      convert hdiv using 1
      · ext j
        rfl
      · rw [add_zero, div_self hm.ne']
    have haclim : Tendsto (fun j ↦ ((a j : ℝ) : ℂ)) atTop (nhds 1) := by
      change Tendsto (Complex.ofReal ∘ a) atTop (nhds 1)
      simpa only [Complex.ofReal_one] using
        Complex.continuous_ofReal.continuousAt.tendsto.comp halim
    have hscaled := haclim.smul hrlim
    simpa only [q, map_smul, one_smul] using hscaled
end

set_option autoImplicit false
open Filter
universe u
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E]
theorem _root_.solution
    (A : E →L[ℂ] E) (S : Set ℂ) (m : ℝ) (hm : 0 ≤ m)
    (G : E →L[ℂ] E) (hGzero : m = 0 → G = 0)
    (r : ℕ → Polynomial ℂ)
    (hr : ∀ j, polynomialSupNorm (r j) S ≤
      m + 1 / ((j : ℝ) + 1))
    (hrlim : Tendsto (fun j ↦ Polynomial.aeval A (r j)) atTop (nhds G)) :
    ∃ q : ℕ → Polynomial ℂ,
      (∀ j, polynomialSupNorm (q j) S ≤ m) ∧
      Tendsto (fun j ↦ Polynomial.aeval A (q j)) atTop (nhds G) := by
  by_cases hm0 : m = 0
  · have hG : G = 0 := hGzero hm0
    refine ⟨fun _ ↦ 0, ?_, ?_⟩
    · intro j
      rw [hm0]
      unfold polynomialSupNorm
      refine Real.iSup_le (fun z ↦ ?_) le_rfl
      exact Real.iSup_le (fun _ ↦ by
        simp only [Polynomial.eval_zero, norm_zero]
        exact le_rfl) le_rfl
    · rw [hG]
      simpa only [map_zero] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0 : E →L[ℂ] E))
          atTop (nhds 0))
  · exact exists_tendsto_polynomial_companions_of_add_one_div_bounds_of_pos
      A S m (lt_of_le_of_ne hm (Ne.symm hm0)) G r hr hrlim
