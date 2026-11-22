-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bridge20261122_UBV_natclock_given_true_discounted_terminal_envelopes
-- name    : AvramDividend.Classical.avram_bridge20261122_UBV_natclock_given_true_discounted_terminal_envelopes
-- status  : Open
-- author  : @WillR
-- created : 2026-11-22T22:12:11.242+00:00
-- url     : https://prove2.me/theorems/a92538ef-310b-48fe-b50f-2a8b5a6ffe6c
-- title:
--   Original UBV stopped natural-horizon budget given two source-faithful discounted terminal vanishing envelopes
-- statement:
--   The original positive-discount UBV natural-horizon discounted dividend Stieltjes bound, with exactly the physical sample P and q, conditional on two independently proved terminal vanishing lemmas: finite stochastic terminal envelope and uniformly bounded expectation of undiscouted payoffs. The genuine original terminal envelope and physical stochastic reward estimate still need to be constructed before the infinite-horizon argument.
-- source:
--   Root-connected Open 61bbf167, plus Proved terminal-limit heads f7c1f646 and d0605a55 and their seven original imported dependencies.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_bridge20261122_UBV_natclock_given_true_discounted_terminal_envelopes
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hDiscountedTerminal : (∀ (Envelope : Ω → ℝ≥0∞) (hEnvelope : Measurable Envelope)
    (hFinite : (∫⁻ ω, Envelope ω ∂P) < ⊤)
    (Terminal : ℕ → Ω → ℝ≥0∞)
    (hBound : ∀ n ω, Terminal n ω ≤
      ENNReal.ofReal (Real.exp (-(q * (n : ℝ)))) * Envelope ω),
Filter.Tendsto (fun n : ℕ => ∫⁻ ω, Terminal n ω ∂P)
      Filter.atTop (nhds (0 : ℝ≥0∞))) ∧
      (∀ (Payoff Terminal : ℕ → Ω → ℝ≥0∞)
    (hPayoff : ∀ n, Measurable (Payoff n))
    (hBound : ∀ n ω, Terminal n ω ≤
      ENNReal.ofReal (Real.exp (-(q * (n : ℝ)))) * Payoff n ω)
    (M : ℝ≥0∞) (hUniform : ∀ n, (∫⁻ ω, Payoff n ω ∂P) ≤ M)
    (hFinite : M ≠ ⊤),
Filter.Tendsto (fun n => ∫⁻ ω, Terminal n ω ∂P)
      Filter.atTop (nhds (0 : ℝ≥0∞)))) :
    ∀ n : ℕ,
      (∫⁻ ω, ∫⁻ t in
          paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)),
          ENNReal.ofReal (Real.exp (-(q * t)))
            ∂(dividendMeasure D ω) ∂P) ≤ ENNReal.ofReal (w x) := by sorry
