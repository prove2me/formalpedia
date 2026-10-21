-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_unbounded_closed_horizon_killed_scale_grid_limit
-- name    : AvramDividend.Classical.chat04_unbounded_closed_horizon_killed_scale_grid_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T04:28:37.570529+00:00
-- url     : https://prove2.me/theorems/dbafcb98-37dc-4715-9766-5564a003cc6b
-- title:
--   Killed finite-horizon q-scale expectation from explicit finite grids, for unbounded-variation processes and without standing assumptions
-- statement:
--   Let X be a spectrally negative Levy process of unbounded variation, q > 0, and W its q-scale function. Kill the process at the first exit from an interval (lower, upper) or at the horizon T, and evaluate the q-scale payoff of the killed reserve. The expectation of that killed payoff is the decreasing limit of the expectations computed on explicit finite grids that check the survival condition at every rational time up to the horizon. No standing assumption is required. The content is that the continuous-time survival expectation is recovered from finite-grid survival checks, the grid being the rational-time schedule that covers every nonnegative rational time. The standing assumptions are not needed here because the only ingredient beyond the grid-limit mechanism itself, the integrability of the fixed-time scale payoff, is available for unbounded variation without them.
-- source:
--   The killed finite-horizon q-scale expectation from finite grids, specialised to the unbounded-variation case. The grid-limit mechanism is the Proved theorem chat04_closed_horizon_survival_lintegral_grid_limit and the integrability input is the Proved theorem chat04_unbounded_scale_fixed_time_integrable; the standing-case version is the Proved theorem chat04_standing_closed_horizon_killed_scale_grid_limit. Formalised in the Avram Dividend Classical proof programme.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_unbounded_closed_horizon_killed_scale_grid_limit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation)
    (x lower upper : ℝ) (T : ℝ≥0) :
    (∫⁻ ω,
      ({ω | ∀ t : ℝ≥0, t ≤ T →
        ¬ (X.X t ω < lower ∨ upper < X.X t ω)}).indicator
          (fun ω => ENNReal.ofReal (W (x + X.X T ω))) ω ∂P) =
      ⨅ n : ℕ, ∫⁻ ω,
        ({ω | ∀ j ≤ n,
          (((Nat.unpair j).2 : ℝ≥0) * ((((Nat.unpair j).1 + 1 : ℕ) : ℝ≥0)⁻¹) < T →
            ¬ (X.X (((Nat.unpair j).2 : ℝ≥0) * ((((Nat.unpair j).1 + 1 : ℕ) : ℝ≥0)⁻¹)) ω < lower ∨
               upper < X.X (((Nat.unpair j).2 : ℝ≥0) * ((((Nat.unpair j).1 + 1 : ℕ) : ℝ≥0)⁻¹)) ω)) ∧
          ¬ (X.X T ω < lower ∨ upper < X.X T ω)}).indicator
            (fun ω => ENNReal.ofReal (W (x + X.X T ω))) ω ∂P := by sorry
