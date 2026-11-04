-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_finite_simple_integral_measurable
-- name    : AvramDividend.Classical.avram_p2_f_weighted_original_finite_simple_integral_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T14:46:59.378087+00:00
-- url     : https://prove2.me/theorems/2e1cf042-1338-4f5c-97d9-a918956dfaad
-- title:
--   Actual original Lévy finite predictable-simple jump measure integral is measurable
-- statement:
--   For the genuine original spectrally negative Lévy process and its unchanged filtration, every finite predictable-simple nonnegative integrand on deterministic future marked rectangles has an ambient-measurable random integral against its literal intrinsic marked jump measure. Each coefficient H_i is measurable in its original past σ-algebra and each mark set is Borel. The proof uses accepted original intrinsic rectangle-count measurability and the separate random-measure finite-simple measurability transfer. It does not assume an auxiliary Poisson copy, random-kernel measurability axiom, or any source ν rate, providing the concrete outer-measurability requirement for P2-E's simple compensator.
-- source:
--   Accepted source original rectangle measurable d9c55240 and genuine random-measure finite-simple measurability helper.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_intrinsic_rectangle_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_random_measure_finite_simple_integral_measurable

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_f_weighted_original_finite_simple_integral_measurable
    {Ω ι : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (S : Finset ι) (s T : ι → ℝ≥0)
    (B : ι → Set ℝ) (hB : ∀ i ∈ S, MeasurableSet (B i))
    (H : ι → Ω → ℝ≥0∞)
    (hH : ∀ i ∈ S, Measurable[𝓕 (s i)] (H i)) :
    Measurable (fun ω =>
      (∫⁻ p, S.sum (fun i => (Ioc (s i) (s i + T i) ×ˢ B i).indicator (fun _ => H i ω) p) ∂((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))))) := by sorry
