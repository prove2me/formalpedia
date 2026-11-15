-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a25_20261115_original_Borel_count_real_charfun_poisson
-- name    : AvramDividend.Classical.avram_a25_20261115_original_Borel_count_real_charfun_poisson
-- status  : Open
-- author  : @WillR
-- created : 2026-11-15T00:01:21.726185+00:00
-- url     : https://prove2.me/theorems/82538c3b-273b-41c9-9dac-3fa56cfa22c1
-- title:
--   Positive-rate original physical Borel negative jump-count has the real Poisson characteristic function
-- statement:
--   The original finite negative-jump-activity Lévy path count of jumps with mark in a negative Borel set, realised measurably by K and with prescribed finite positive rate r, has the characteristic function of a Poisson(r) integer count embedded into the real line. This statement is on the given original probability space; it makes no new Poisson driver or independent companion and supplies the remaining characteristic-function identity sufficient for the target exact singleton probabilities.
-- source:
--   Lévy–Khintchine and original-path negative Borel jump-count Poisson process properties; use the proved characteristic-function uniqueness theorem FamousTheorems.char_fun_determines_measure_6b to recover target a115 via real Nat-cast injectivity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a25_20261115_original_Borel_count_real_charfun_poisson
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (T : ℝ≥0) (B : Set ℝ)
    (hB : MeasurableSet B) (hNeg : B ⊆ Iio (0 : ℝ))
    (K : Ω → ℕ) (hK : Measurable K)
    (hCount : ∀ᵐ ω ∂P, (K ω : ℝ) =
      (((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ B)).toReal)
    (r : ℝ≥0)
    (hr : (r : ℝ) = ((T : ℝ≥0∞) * X.ν B).toReal)
    (hRatePos : 0 < r) :
    ∀ u : ℝ,
      charFun (P.map (fun ω => (K ω : ℝ))) u =
        charFun ((poissonMeasure r).map (fun n : ℕ => (n : ℝ))) u := by sorry
