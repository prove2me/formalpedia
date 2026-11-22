-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_twoagentA_original_allnu_finite_reciprocal_L2_integrable_public
-- name    : AvramDividend.Classical.avram_twoagentA_original_allnu_finite_reciprocal_L2_integrable_public
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T12:23:15.462622+00:00
-- url     : https://prove2.me/theorems/9fee3d02-3890-4671-95dc-c85c1a9b62c5
-- title:
--   Importable all-activity original finite reciprocal compensated physical jump mesh L2 integrability
-- statement:
--   For any original spectrally negative Levy sample path and any deterministic horizon, prove finite reciprocal negative-mark annular compensated actual jump-count sums have integrable square under the original law. Same original process X and Levy measure, no finite jump activity, synthetic noise or supplied stochastic isometry. Lean proof adapted directly from independently Proved Worker B source e0e20d45, published for reuse across workers.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ja34_original_finite_borel_mark_simple_sum_square_integrable
open MeasureTheory Set AvramDividend.Classical
open scoped Classical NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_twoagentA_original_allnu_finite_reciprocal_L2_integrable_public
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (n m : ℕ) (hnm : n ≤ m) :
    let B : ℕ → Set ℝ := fun i =>
      Ioc (-(1 / ((i : ℝ) + 1))) (-(1 / ((i : ℝ) + 2)))
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    let r : ℕ → ℝ := fun i => ((T : ℝ≥0∞) * X.ν (B i)).toReal
    let S : Ω → ℝ := fun ω =>
      ∑ i ∈ Finset.Ico n m,
        (-(1 / ((i : ℝ) + 1))) *
          ((NX ω (Ioc 0 T ×ˢ B i)).toReal - r i)
    Integrable (fun ω => (S ω) ^ 2) P := by sorry
