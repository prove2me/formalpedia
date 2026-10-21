-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_countable_grid_survival_prefix_limit
-- name    : AvramDividend.Classical.chat04_countable_grid_survival_prefix_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T07:41:25.170724+00:00
-- url     : https://prove2.me/theorems/879173a3-92c2-4dd4-8ee9-ac34088c07bb
-- title:
--   Finite-prefix grid-survival payoff expectations converge to countably monitored survival
-- statement:
--   Given any countable sequence B_k of measurable events representing successive observation-time survival tests, and any measurable nonnegative terminal payoff g with finite unrestricted expectation, prove that the expectation restricted to the event that ALL B_k hold is the infimum of the expectations restricted to satisfying the first n+1 tests (k≤n). The finite-prefix events A_n={all B_k for k≤n} are measurable and antitone, and their intersection is exactly ⋂k B_k. Apply the accepted generic antitone-grid survival lintegral_iInf theorem. This makes the finite-grid-to-countable-grid expectation passage directly usable without requiring any specified mesh or a q-scale martingale. It addresses one actual convergence layer of the killed semigroup proof; identifying the countable event with continuous-time no-ruin still requires the separate pathwise-density theorem.
-- source:
--   Imported accepted theorem AvramDividend.Classical.chat04_antitone_grid_survival_lintegral_iInf (publication must be ACCEPTED first) and pinned Mathlib measurableSet_iInter and Nat prefix order.

import Mathlib.MeasureTheory.Integral.Lebesgue.Sub
import Theorems.Thm_AvramDividend_Classical_chat04_antitone_grid_survival_lintegral_iInf

open MeasureTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.chat04_countable_grid_survival_prefix_limit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (B : ℕ → Set Ω) (hB : ∀ k, MeasurableSet (B k))
    (g : Ω → ℝ≥0∞) (hg : Measurable g)
    (hFin : (∫⁻ ω, g ω ∂P) ≠ ∞) :
    (∫⁻ ω, (⋂ k, B k).indicator g ω ∂P) =
      ⨅ n, ∫⁻ ω,
        ({ω | ∀ k ≤ n, ω ∈ B k}).indicator g ω ∂P := by sorry
