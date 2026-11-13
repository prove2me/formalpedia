-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b20_bvb23_real_index_terminal_indicator_tendsto
-- name    : AvramDividend.Classical.avram_b20_bvb23_real_index_terminal_indicator_tendsto
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T16:20:16.088197+00:00
-- url     : https://prove2.me/theorems/70a96dcf-1dca-4a88-a6cf-132ca6f63bed
-- title:
--   Real-indexed stopped terminal cutoff converges away from the original ruin clock
-- statement:
--   For the positive physical time t strictly below horizon T and unequal to ruin time, the original strict positive-time and weak pre-ruin time gate with endpoint T-T/(n+2), indexed by REAL n tending to infinity, eventually agrees with the strict pre-ruin rate gate. This is the exact real-indexed second branch in the original bvb_b23 A/K pointwise theorem. Earlier Nat-index source lemma e384d815 has a different index type and cannot be used directly.
-- source:
--   Direct order-theoretic eventual cutoff using archimedean atTop on real n, positive gap T-t, and neq ruin to convert weak survival to strict survival. It proves a distinct indexing type overlooked by existing Nat-index limit source.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_b20_bvb23_real_index_terminal_indicator_tendsto
    (T : ℝ) (hT : 0 < T) (τ : ℝ≥0∞) (t : ℝ≥0)
    (ht0 : 0 < t) (htT : (t : ℝ) < T)
    (hτ : (t : ℝ≥0∞) ≠ τ)
    (C : ℝ≥0∞) (b v : ℝ) :
    Tendsto (fun n : ℝ =>
      if 0 < t ∧ (t : ℝ) < T - T / (n + 2) ∧
        (t : ℝ≥0∞) ≤ τ ∧ 0 ≤ b ∧ ENNReal.ofReal b ≤ C
      then v else 0)
      atTop (nhds (if (t : ℝ≥0∞) < τ ∧
        0 ≤ b ∧ ENNReal.ofReal b ≤ C then v else 0)) := by sorry
