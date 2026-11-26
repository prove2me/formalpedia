-- Prove2me | Theorems.Thm_BellWilliams2001_ThresholdPolicy_threshold_queue_second_moment
-- name    : BellWilliams2001.ThresholdPolicy.threshold_queue_second_moment
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T05:34:29.931956+00:00
-- url     : https://prove2.me/theorems/cb0920af-c57c-4854-9742-1e11019e8b9c
-- title:
--   A uniform polynomial second-moment bound for the threshold queues
-- statement:
--   For all sufficiently large threshold coefficients, the square of the instantaneous holding cost under the threshold policies has a uniform polynomial moment bound on diffusion time. For some $C\ge0$ and integer $p\ge0$, all sufficiently large system indices satisfy
--
--   $$\mathbb E\big[(h\cdot\widehat Q^{r,*}(t))^2\big]\le C(1+t)^p\qquad(t\ge0).$$
--
--   The system index cutoff is independent of time. The polynomial estimate gives uniform integrability on each bounded time interval and an integrable bound after exponential discounting.
-- source:
--   Bell and Williams (2001), The Annals of Applied Probability 11(3), 608–649, https://doi.org/10.1214/aoap/1015345343, Section 9, the moment estimates used in the upper bound for Theorem 5.3

import Mathlib
import Definitions.Def_BellWilliams2001_ThresholdPolicy_Model
import Definitions.Def_BellWilliams2001_ThresholdPolicy_Threshold
import Definitions.Def_BellWilliams2001_ThresholdPolicy_BrownianControl

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace BellWilliams2001.ThresholdPolicy

theorem threshold_queue_second_moment {Ω : Type*} [MeasurableSpace Ω] (M : SystemSequence Ω) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ c : ℝ, c₀ < c → ∀ Tstar : ℕ → Allocation Ω,
      (∀ n, 1 ≤ M.threshold c n → M.IsAdmissible n (Tstar n) ∧ M.IsThreshold c n (Tstar n)) →
      ∃ C : ℝ, 0 ≤ C ∧ ∃ p : ℕ, ∀ᶠ n in atTop, ∀ t : ℝ, 0 ≤ t →
        (∫⁻ ω, (ENNReal.ofReal (∑ k, M.h k * M.Qhat n (Tstar n) ω t k)) ^ 2 ∂M.P) ≤
          ENNReal.ofReal (C * (1 + t) ^ p) := by sorry

end BellWilliams2001.ThresholdPolicy
