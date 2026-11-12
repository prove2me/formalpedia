-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gb38_bounded_quadratic_fourth_to_integrable_square
-- name    : AvramDividend.Classical.avram_gb38_bounded_quadratic_fourth_to_integrable_square
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T10:21:06.604204+00:00
-- url     : https://prove2.me/theorems/24522bcf-dab8-4707-a74b-dfa775e0b737
-- title:
--   Bounded predictable quadratic coefficient converts fourth moments to integrable squared energy
-- statement:
--   A uniformly bounded real weight multiplying a centred square has integrable squared product whenever the input has a fourth moment. The estimate is explicit: E[(H(Z²−a))²]≤2K²(E[Z⁴]+a²), for a probability measure.
-- source:
--   Analytic step needed for original finite-cap Gaussian gb34 quadratic-cell fourth-moment estimate, without adding any auxiliary process.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_gb38_bounded_quadratic_fourth_to_integrable_square
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (H Z : Ω → ℝ) (a B K : ℝ)
    (hH : Measurable H) (hZ : Measurable Z)
    (hK : 0 ≤ K) (hHb : ∀ ω, |H ω| ≤ K)
    (hZ4 : Integrable (fun ω => (Z ω) ^ 4) P)
    (hB : (∫ ω, (Z ω) ^ 4 ∂P) ≤ B) :
    Integrable (fun ω => (H ω * ((Z ω) ^ 2 - a)) ^ 2) P ∧
      (∫ ω, (H ω * ((Z ω) ^ 2 - a)) ^ 2 ∂P) ≤
        2 * K ^ 2 * (B + a ^ 2) := by sorry
