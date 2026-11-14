-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b123_original_actual_jumpfree_implies_every_negative_count_zero
-- name    : AvramDividend.Classical.avram_b123_original_actual_jumpfree_implies_every_negative_count_zero
-- status  : Open
-- author  : @WillR
-- created : 2026-11-13T17:24:25.763104+00:00
-- url     : https://prove2.me/theorems/92e0db8f-ece4-4e44-9104-b8edb1c69cb8
-- title:
--   Any truly jumpfree original physical time interval has zero original negative Poisson count at every cutoff
-- statement:
--   For the exact original spectrally negative Lévy source and any physical half-open interval (s,t], if every actual source jump increment in that interval is zero, then the original mapped negative-jump Poisson measure assigns mass zero to its rectangle with any original reciprocal negative mark cutoff. The Proved exact original interval-band count equals the cardinality of actual marked source jump times, which is zero because the marked set is empty. This is the reverse physical/count bridge to B110, giving the exact zero-count semantics needed to identify genuine unmarked stopped-grid cells in the Itô source.
-- source:
--   Proved original P2-E exact marked Poisson rectangle count equals actual negative-band jump time ncard.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_original_interval_negative_band_count_ncard
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- On an actually jumpfree original source interval every finite negative-mark Poisson cutoff count is zero. -/

theorem AvramDividend.Classical.avram_b123_original_actual_jumpfree_implies_every_negative_count_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (s t : ℝ≥0) (hst : s ≤ t)
    (hNoJump : ∀ u : ℝ≥0, s < u → u ≤ t →
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u = 0)
    (n : ℕ) :
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s t ×ˢ Iic (-(1 / ((n : ℝ) + 1)))) = 0 := by sorry
