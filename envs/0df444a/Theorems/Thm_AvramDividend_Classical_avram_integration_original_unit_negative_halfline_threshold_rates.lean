-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_integration_original_unit_negative_halfline_threshold_rates
-- name    : AvramDividend.Classical.avram_integration_original_unit_negative_halfline_threshold_rates
-- status  : Open
-- author  : @WillR
-- created : 2026-11-04T00:57:37.540076+00:00
-- url     : https://prove2.me/theorems/6169a734-f844-4e24-b278-0713a6f113b9
-- title:
--   Original unit-time Lévy rate on cutoff and lower-halfline generating tests
-- statement:
--   For a genuine original Lévy path, unit-time intrinsic expected marked jump counts agree with the original Lévy measure on the cutoff half-line (-∞,-ε] and on every stricter lower half-line (-∞,a] for a<−ε. This is a sufficient generating-class input for the independently proved original marked-measure Borel extension and is the outstanding analytic threshold-rate lemma; it assumes no Campbell or intensity conclusion.
-- source:
--   Exact unit-time negative-threshold analytic bridge. Available separate Proved source: compact-negative continuous-test jump first moment 2e2ebbae and marginal version c3a1882e. Proved measure extension 66c93dd8 handles arbitrary Borel B once these threshold identities are established.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_integration_original_unit_negative_halfline_threshold_rates
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ε : ℝ) (hε : 0 < ε) :
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 (1 : ℝ≥0) ×ˢ Iic (-ε)) ∂P) = X.ν (Iic (-ε)) ∧
    ∀ a : ℝ, a < -ε →
      (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 (1 : ℝ≥0) ×ˢ Iic a) ∂P) = X.ν (Iic a) := by sorry
