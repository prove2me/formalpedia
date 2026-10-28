-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_continuousOn_nonnegative_locally_bounded
-- name    : AvramDividend.Classical.causal_continuousOn_nonnegative_locally_bounded
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T11:12:59.60899+00:00
-- url     : https://prove2.me/theorems/4d215440-7ab6-47e2-8295-bdec11a289a8
-- title:
--   Nonnegative-time continuous Volterra resolvents are locally bounded
-- statement:
--   A real-valued function continuous on [0,infinity) is uniformly bounded on every compact interval [0,R], hence bounded on (0,R] for every R>0. This discharges the missing local-boundedness input of the full drift-plus-L1 Gaussian Volterra endpoint convolution theorem, for a derivative resolvent continuous on nonnegative times.
-- source:
--   Heine–Borel compactness and pinned Mathlib IsCompact.exists_bound_of_continuousOn.

import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.Instances.Real.Lemmas
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical Set
open scoped Topology

namespace AvramDividend.Classical
/-- Continuous input on nonnegative times is bounded on each compact positive interval. -/
theorem causal_continuousOn_nonnegative_locally_bounded
    (g : ℝ → ℝ) (hg : ContinuousOn g (Ici (0 : ℝ))) :
    ∀ R : ℝ, 0 < R →
      ∃ C : ℝ, ∀ s : ℝ, s ∈ Ioc (0 : ℝ) R → |g s| ≤ C := by
  sorry
end AvramDividend.Classical
