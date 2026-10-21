-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_standing_closed_horizon_killed_scale_grid_limit
-- name    : AvramDividend.Classical.chat04_standing_closed_horizon_killed_scale_grid_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T22:44:04.255423+00:00
-- url     : https://prove2.me/theorems/ad3c4b03-d5a3-411a-8f3c-f25a99fdfde9
-- title:
--   Killed finite-horizon q-scale expectation from explicit finite Cantor grids under Standing
-- statement:
--   For any spectrally negative Lévy process satisfying the exact Avram Standing assumptions, positive q, canonical q-scale W, real initial reserve x, strict lower and upper barriers and finite horizon T, the expected scale payoff W(x+X_T) killed if the path crosses either strict barrier at any time in the CLOSED interval [0,T] equals the decreasing infimum of finite-prefix Cantor-grid expectation values. Each finite prefix monitors the schedule points before T and the terminal state at T, so boundary crossing at the terminal time cannot be omitted. No separate integrability, schedule-density or null fixed-time event assumption is required. The result is the exact finite-horizon killed-expectation interface needed for a future proof of the q-scale martingale, but does not assert q-harmonicity itself.
-- source:
--   Accepted Chat04 nat_pairing_rational_grid_coverage UUID 34d1a207-11c0-49d1-b331-c905323990f4, accepted standing_scale_fixed_time_integrable UUID 1d43ef79-1a69-4d82-b4de-d9ad5d5c8ee5, accepted full-line scale Borel measurable UUID 45cbe3b4-374d-4fa4-b988-e09f93b74cab, and pending closed_horizon_survival_lintegral_grid_limit.

import Mathlib.Data.Nat.Pairing
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat04_nat_pairing_rational_grid_coverage
import Theorems.Thm_AvramDividend_Classical_chat04_closed_horizon_survival_lintegral_grid_limit
import Theorems.Thm_AvramDividend_Classical_chat04_standing_scale_fixed_time_integrable
import Theorems.Thm_AvramDividend_Classical_chat03_scale_function_borel_measurable

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_standing_closed_horizon_killed_scale_grid_limit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
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
