-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_killed_scale_fixed_time_integrable
-- name    : AvramDividend.Classical.chat03_killed_scale_fixed_time_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T10:51:41.068091+00:00
-- url     : https://prove2.me/theorems/dc9ef8a9-34f0-4522-a76c-d2cc20fdbce1
-- title:
--   Fixed-time integrability of the continuously downward-killed discounted scale payoff
-- statement:
--   Under the exact Avram standing assumptions, any positive discount rate and a q-scale function, the q-discounted scale payoff killed if the shifted Lévy reserve crossed below zero at any moment through a finite time t is integrable. It follows from the previously Proved integrability of the full-line terminal scale function, measurable continuous-history survival via reciprocal-natural-grid downward-crossing and preservation of integrability under multiplication by a fixed scalar and restriction to a measurable event. Together with killed-payoff adaptedness, this discharges two components of the required killed-martingale proof; the conditional expectation identity remains open.
-- source:
--   Uses Proved chat04_standing_scale_fixed_time_integrable (1d43ef79-1a69-4d82-b4de-d9ad5d5c8ee5) and newly Proved chat03_lower_survival_filtration_measurable (398891d8-81c2-4654-864c-79b2496d4c95). Does not assume the killed martingale.

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Mathlib.MeasureTheory.Function.L1Space.Integrable

open MeasureTheory Set
open scoped NNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat03_killed_scale_fixed_time_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (τ : ℕ → ℝ≥0)
    (hCover : ∀ n : ℕ, 0 < n → ∀ k : ℕ,
      ∃ j : ℕ, τ j = (k : ℝ≥0) * (n : ℝ≥0)⁻¹)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (x : ℝ) (t : ℝ≥0) :
    Integrable
      (({ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω}).indicator
        (fun ω => Real.exp (-(q * (t : ℝ))) *
          W (x + X.X t ω))) P := by
  sorry
