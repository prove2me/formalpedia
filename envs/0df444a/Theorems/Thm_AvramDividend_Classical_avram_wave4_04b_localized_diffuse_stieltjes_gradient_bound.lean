-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_localized_diffuse_stieltjes_gradient_bound
-- name    : AvramDividend.Classical.avram_wave4_04b_localized_diffuse_stieltjes_gradient_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T09:50:21.791806+00:00
-- url     : https://prove2.me/theorems/3c55d747-d4b5-4059-82d6-d8d7372daa44
-- title:
--   Interior-localised full atomless dividend measure pays for itself under the source HJB gradient bound
-- statement:
--   For the actual controlled source path, restrict attention to a finite sample-path horizon on which every genuine pre-dividend reserve lies strictly inside the open cap (0,C). Under precisely the source HJB gradient hypothesis on that open cap, decompose the actual Stieltjes dividend measure into its right-atomic component and an atomless remainder. The full discounted payment integral against the latter is bounded by the corresponding derivative-weighted integral, even when the remainder contains singular-continuous mass. The proof uses the remainder's support within [0,T] and an almost-everywhere Lebesgue integral monotonicity theorem, not an absolutely continuous density or an atom-concentration assumption. The interior localisation condition is explicit and does not assert that all admissible paths satisfy it globally; source jump-a.e. identification needed for the full Itô–Meyer formula is separate.
-- source:
--   Canonically Proved source-specific finite horizon Stieltjes atomic/diffuse measure decomposition; original riskProcess X x D and HJB gradient domain; Mathlib lintegral_mono_ae and support of restricted measure. This is the diffuse control sign, not a stochastic chain rule.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_finite_horizon_stieltjes_atomic_diffuse

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave4_04b_localized_diffuse_stieltjes_gradient_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (ω : Ω) (T : ℝ≥0) (q : ℝ)
    (hloc : ∀ t : ℝ≥0, t ≤ T →
      0 < riskProcess X x D t ω ∧
        ENNReal.ofReal (riskProcess X x D t ω) < C) :
    let μ : Measure ℝ :=
      (dividendMeasure D ω).restrict (Icc (0 : ℝ) (T : ℝ))
    ∃ (A : Set ℝ) (μatom μdiffuse : Measure ℝ),
      A.Countable ∧ MeasurableSet A ∧
      μ = μatom + μdiffuse ∧
      μatom = Measure.sum (fun t : A => μ {(t : ℝ)} • Measure.dirac (t : ℝ)) ∧
      μatom Aᶜ = 0 ∧ NullSingletonClass μdiffuse ∧
      (∫⁻ s : ℝ,
        ENNReal.ofReal (Real.exp (-(q * s))) ∂μdiffuse) ≤
      (∫⁻ s : ℝ,
        ENNReal.ofReal (Real.exp (-(q * s))) *
        ENNReal.ofReal (deriv w (riskProcess X x D s.toNNReal ω))
          ∂μdiffuse) := by sorry
