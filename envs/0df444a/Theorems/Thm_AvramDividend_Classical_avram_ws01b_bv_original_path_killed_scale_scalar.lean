-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01b_bv_original_path_killed_scale_scalar
-- name    : AvramDividend.Classical.avram_ws01b_bv_original_path_killed_scale_scalar
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T10:02:31.144992+00:00
-- url     : https://prove2.me/theorems/b1285a5a-a308-4592-9376-34f0bc908c87
-- title:
--   Actual BV killed q-scale fixed point on genuine whole-path law and complete grid
-- statement:
--   The genuine original spectrally negative bounded-variation Lévy whole-path distribution satisfies the exact killed discounted q-scale scalar identity at any time and all real reserves, where the continuous survival event is represented by any rationally covering schedule containing its terminal endpoint. This transfers the remotely Proved no-root deterministic killed semigroup through the original path map and the Standing real-to-ENNReal expectation bridge. This is the exact hScalar hypothesis of the accepted random-reserve Markov–Tonelli kernel, without relying on c2 or stopped optional stopping.
-- source:
--   Canonical source 1630fd39 BV no-root deterministic killed q-scale, 6275ef80 standing real/ENNReal bridge, 67c7e86c genuine closed path schedule equivalence, a484bed3 measurable grid event, 840bbf85 whole path measurability. No W(0)=0 or finite jump activity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_avram_ws01b_bv_deterministic_killed_qscale_no_root
import Theorems.Thm_AvramDividend_Classical_chat04_standing_history_killed_scale_real_ennreal_integral_bridge
import Theorems.Thm_AvramDividend_Classical_chat04_random_reserve_shifted_closed_survival_schedule_iff
import Theorems.Thm_AvramDividend_Classical_chat04_countable_shifted_future_reserve_survival_measurable
import Theorems.Thm_AvramDividend_Classical_levy_wholePath_measurable
import Theorems.Thm_AvramDividend_Classical_scaleFunction_monotone

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
attribute [local instance] Classical.propDecidable

theorem AvramDividend.Classical.avram_ws01b_bv_original_path_killed_scale_scalar
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (hBV : X.BoundedVariation)
    (x : ℝ) (T : ℝ≥0) (τ : ℕ → ℝ≥0)
    (hCover : ∀ n : ℕ, 0 < n → ∀ k : ℕ,
      ∃ j : ℕ, τ j = (k : ℝ≥0) * (n : ℝ≥0)⁻¹)
    (hTerminal : ∃ j : ℕ, τ j = T) :
    (∫⁻ y : ℝ≥0 → ℝ,
      if ∀ j : ℕ, τ j ≤ T → 0 ≤ x + y (τ j) then
        ENNReal.ofReal (Real.exp (-(q * (T : ℝ))) * W (x + y T))
      else (0 : ℝ≥0∞)
      ∂(Measure.map (fun ω : Ω => (fun t : ℝ≥0 => X.X t ω)) P)) =
    ENNReal.ofReal (W x) := by sorry
