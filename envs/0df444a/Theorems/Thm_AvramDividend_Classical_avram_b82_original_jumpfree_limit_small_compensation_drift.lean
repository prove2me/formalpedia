-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b82_original_jumpfree_limit_small_compensation_drift
-- name    : AvramDividend.Classical.avram_b82_original_jumpfree_limit_small_compensation_drift
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T08:11:41.138012+00:00
-- url     : https://prove2.me/theorems/bb95ad17-e568-4686-92ae-393e94147fc0
-- title:
--   Original limiting compensated small negative marks reduce to ν first-moment drift on jumpfree source interval
-- statement:
--   For the actual original finite-activity compensated small-negative-band source, B80 proves that on an interval with no original physical negative source mark the compensated finite-band increment is exactly minus elapsed real time times the original restricted negative-mark first moment. If the original truncated small-band processes converge at every physical source clock to the given intrinsic Jsmall and the restricted original ν first moment converges to its limiting compensator drift d, then passage to the limit is legitimate by continuity of subtraction and multiplication in the real line and uniqueness of the limit. Thus the original Jsmall increment equals d times elapsed physical time, exactly the hSmall hypothesis of B78, at any (including random) source clock whose original X path has no jump between endpoints. The two convergence hypotheses are explicit mathematical obligations. Finite negative-jump activity is expected to yield the ν convergence by finite mass and domination on the bounded negative strip, but this theorem does not silently assume it. Exceptional sample paths must be handled by a totalised source definition or restricted almost-everywhere equality before applying global B78.
-- source:
--   Avram Palmowski Pistorius (2007) Proposition 4(i), original B80 finite negative-mark band compensator identity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_b80_original_jumpfree_cell_smallband_compensator_increment
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_b82_original_jumpfree_limit_small_compensation_drift
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (Jsmall : ℝ≥0 → Ω → ℝ)
    (hJlim : ∀ ω u, Tendsto
      (fun n => avram_p4_h_gaussian_intrinsic_small_band_compensated X n u ω)
      atTop (𝓝 (Jsmall u ω)))
    (d : ℝ)
    (hνlim : Tendsto (fun n : ℕ =>
      -(∫ z in Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1))), z ∂X.ν))
      atTop (𝓝 d))
    (s t : Ω → ℝ≥0)
    (hOrder : ∀ ω, s ω ≤ t ω)
    (hNoJump : ∀ ω (u : ℝ≥0), s ω < u → u ≤ t ω →
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u = 0) :
    ∀ ω, Jsmall (t ω) ω - Jsmall (s ω) ω =
      d * ((t ω : ℝ) - (s ω : ℝ)) := by sorry
