-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_standing_cantor_grid_survival_scale_limit
-- name    : AvramDividend.Classical.chat04_standing_cantor_grid_survival_scale_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T10:08:00.551456+00:00
-- url     : https://prove2.me/theorems/961637cb-fb57-4766-b211-d004a0d9ce35
-- title:
--   Continuous-time survival q-scale expectation from finite Cantor-grid checks under Standing
-- statement:
--   For a spectrally negative Lévy process under the exact Standing assumptions, q>0, canonical q-scale W, arbitrary real x and strict lower/upper thresholds, the expected nonnegative fixed-horizon q-scale payoff W(x+X_T) multiplied by genuine continuous-time survival equals the decreasing infimum of expectations restricted to survival at the first n observation times in the explicit Cantor-paired rational schedule τ(j)=(unpair j).2/((unpair j).1+1). This formalises the continuous-time killed expectation limit from finite-grid monitoring, with no assumed integrability, no auxiliary schedule coverage and no path-continuity gaps. It combines separately accepted exact reciprocal-grid coverage, pathwise strict survival detection and continuity from above, while fixed-time integrability is derived from the accepted Standing theorem. The martingale/q-harmonicity remains a separate open goal.
-- source:
--   Accepted Chat04 theorems chat04_nat_pairing_rational_grid_coverage 34d1a207-11c0-49d1-b331-c905323990f4, chat04_countable_grid_strict_survival_event_eq 2d1d4d5d-72ab-4e14-aedc-4018903df231, chat04_countable_grid_survival_prefix_limit 879173a3-92c2-4dd4-8ee9-ac34088c07bb, chat04_standing_scale_fixed_time_integrable 1d43ef79-1a69-4d82-b4de-d9ad5d5c8ee5, Borel q-scale 45cbe3b4-374d-4fa4-b988-e09f93b74cab, Mathlib lintegral_ofReal_ne_top_iff_integrable.

import Mathlib.Data.Nat.Pairing
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat04_nat_pairing_rational_grid_coverage
import Theorems.Thm_AvramDividend_Classical_chat04_countable_grid_strict_survival_event_eq
import Theorems.Thm_AvramDividend_Classical_chat04_countable_grid_survival_prefix_limit
import Theorems.Thm_AvramDividend_Classical_chat04_standing_scale_fixed_time_integrable
import Theorems.Thm_AvramDividend_Classical_chat03_scale_function_borel_measurable

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_standing_cantor_grid_survival_scale_limit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (x lower upper : ℝ) (T : ℝ≥0) :
    (∫⁻ ω,
      ({ω | ∀ t : ℝ≥0,
        ¬ (X.X t ω < lower ∨ upper < X.X t ω)}).indicator
          (fun ω => ENNReal.ofReal (W (x + X.X T ω))) ω ∂P) =
      ⨅ n : ℕ, ∫⁻ ω,
        ({ω | ∀ j ≤ n,
          ¬ (X.X (((Nat.unpair j).2 : ℝ≥0) *
            ((((Nat.unpair j).1 + 1 : ℕ) : ℝ≥0)⁻¹)) ω < lower ∨
              upper < X.X (((Nat.unpair j).2 : ℝ≥0) *
            ((((Nat.unpair j).1 + 1 : ℕ) : ℝ≥0)⁻¹)) ω)}).indicator
          (fun ω => ENNReal.ofReal (W (x + X.X T ω))) ω ∂P := by sorry
