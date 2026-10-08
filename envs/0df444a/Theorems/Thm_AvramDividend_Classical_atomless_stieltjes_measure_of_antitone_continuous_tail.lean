-- Prove2me | Theorems.Thm_AvramDividend_Classical_atomless_stieltjes_measure_of_antitone_continuous_tail
-- name    : AvramDividend.Classical.atomless_stieltjes_measure_of_antitone_continuous_tail
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T07:24:17.257511+00:00
-- url     : https://prove2.me/theorems/edd43c42-6730-418f-885a-df08e8d845d2
-- title:
--   Construct an atomless Stieltjes measure from a continuous antitone positive tail
-- statement:
--   For a continuous nonnegative decreasing real tail function g on the entire real line, tending to zero at +infinity, the Stieltjes measure of F=-g is atomless, has finite upper tails and satisfies μ([x,∞))=g(x) for every x. This is an analytic component of the alternative logarithmic-derivative construction for excursion-height laws, though a general excursion tail can be unbounded near zero and requires a localisation extension of the lemma.
-- source:
--   Pinned Mathlib StieltjesFunction.measure_Ici, measure_singleton, ContinuousWithinAt.leftLim_eq and ENNReal.toReal_ofReal; Lebesgue–Stieltjes construction.

import Mathlib
open MeasureTheory Set Filter
open scoped Topology ENNReal

theorem AvramDividend.Classical.atomless_stieltjes_measure_of_antitone_continuous_tail
    (g : ℝ → ℝ) (hcont : Continuous g)
    (hanti : Antitone g) (hnonneg : ∀ x : ℝ, 0 ≤ g x)
    (hlim : Tendsto g atTop (𝓝 (0 : ℝ))) :
    ∃ μ : Measure ℝ,
      NullSingletonClass μ ∧
      (∀ x : ℝ, μ (Ici x) ≠ ⊤) ∧
      (∀ x : ℝ, μ.real (Ici x) = g x) := by sorry
