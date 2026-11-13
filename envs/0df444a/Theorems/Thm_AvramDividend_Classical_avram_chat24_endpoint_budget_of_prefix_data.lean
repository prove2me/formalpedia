-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_chat24_endpoint_budget_of_prefix_data
-- name    : AvramDividend.Classical.avram_chat24_endpoint_budget_of_prefix_data
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T07:59:59.690494+00:00
-- url     : https://prove2.me/theorems/208de74a-c2cb-41b5-8fea-07bef454cb5b
-- title:
--   AvramDividend.Classical.avram_chat24_endpoint_budget_of_prefix_data
-- statement:
--   Automatically extracted helper theorem AvramDividend.Classical.avram_chat24_endpoint_budget_of_prefix_data from oversized parent candidate d06891b20bcf74e83e820d9ce7e29fcd3edb348e2a0c9ad00d47135ca4f77295.
-- source:
--   candidate-decomposition:2b85e13a-39e1-480f-b827-ab358b597b5c:d06891b20bcf74e83e820d9ce7e29fcd3edb348e2a0c9ad00d47135ca4f77295

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal

noncomputable section
theorem AvramDividend.Classical.avram_chat24_endpoint_budget_of_prefix_data
    (σ : ℝ≥0∞) (S : ℝ≥0) (initial : ℝ)
    (K V R : ℝ≥0 → ℝ) (Kstop : ℝ) (hS : 0 < S)
    (hp : ∀ B : ℝ≥0, 0 < B → B ≤ S → (B : ℝ≥0∞) < σ →
      K B + V B ≤ initial + R B)
    (hc : 0 < σ → σ ≤ (S : ℝ≥0∞) →
      ∃ (u : ℕ → ℝ≥0) (l : ℝ),
        (∀ n, 0 < u n ∧ u n ≤ S ∧ (u n : ℝ≥0∞) < σ) ∧
        Tendsto (fun n => K (u n) + V (u n) - R (u n)) atTop (nhds l) ∧
        Kstop - R (min σ (S : ℝ≥0∞)).toNNReal ≤ l)
    (hz : σ = 0 → Kstop ≤ initial + R (min σ (S : ℝ≥0∞)).toNNReal)
    (hs : (S : ℝ≥0∞) < σ → Kstop = K S) :
    Kstop + (if (S : ℝ≥0∞) < σ then V S else 0) ≤
      initial + R (min σ (S : ℝ≥0∞)).toNNReal := by sorry
end
