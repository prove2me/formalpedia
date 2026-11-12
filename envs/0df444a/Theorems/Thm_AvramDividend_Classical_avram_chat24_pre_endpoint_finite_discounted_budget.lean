-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_chat24_pre_endpoint_finite_discounted_budget
-- name    : AvramDividend.Classical.avram_chat24_pre_endpoint_finite_discounted_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T00:08:45.725205+00:00
-- url     : https://prove2.me/theorems/7c8dd92b-3898-4ad1-8bde-82844e15f014
-- title:
--   AvramDividend.Classical.avram_chat24_pre_endpoint_finite_discounted_budget
-- statement:
--   Automatically extracted helper theorem AvramDividend.Classical.avram_chat24_pre_endpoint_finite_discounted_budget from oversized parent candidate c1a8585d59e2260a34551ba02f1fc0196aa5cada2afaca89b54c9ef895880c67.
-- source:
--   candidate-decomposition:f8123fbf-cb94-45e8-aca8-e21f50ba9d61:c1a8585d59e2260a34551ba02f1fc0196aa5cada2afaca89b54c9ef895880c67

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set Filter Finset AvramDividend.Classical
open scoped NNReal ENNReal Classical

noncomputable section
theorem AvramDividend.Classical.avram_chat24_pre_endpoint_finite_discounted_budget
    (n : ℕ) (e u z d : ℕ → ℝ) (w : ℝ → ℝ)
    (cash err : ℝ)
    (he : ∀ i, i < n → 0 ≤ e (i + 1))
    (hdiv : ∀ i, i < n → d i ≤ w (z i) - w (u (i + 1)))
    (hcash : cash ≤ (∑ i ∈ Finset.range n, e (i + 1) * d i) + err) :
    cash + e n * w (u n) ≤ e 0 * w (u 0) +
      (∑ i ∈ Finset.range n,
        ((e (i + 1) - e i) * w (u i) +
          e (i + 1) * (w (z i) - w (u i)))) + err := by sorry
end
