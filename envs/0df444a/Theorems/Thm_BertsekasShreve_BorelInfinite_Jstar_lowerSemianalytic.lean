-- Prove2me | Theorems.Thm_BertsekasShreve_BorelInfinite_Jstar_lowerSemianalytic
-- name    : BertsekasShreve.BorelInfinite.Jstar_lowerSemianalytic
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T04:16:33.918105+00:00
-- url     : https://prove2.me/theorems/e685f84e-a8e1-4089-9765-83a111c0b65f
-- title:
--   Corollary 9.4.1 — the optimal cost J* is lower semianalytic
-- statement:
--   Let (SM) satisfy one of (P), (N) or (D). Then the optimal cost function
--   $$J^* : S \to R^*, \qquad J^*(x) = \inf_{\pi \in \Pi'} J_\pi(x),$$
--   is lower semianalytic: $\{x \in S \mid J^*(x) < c\}$ is an analytic subset of $S$ for every $c \in \mathbb R$.
--
--   $J^*$ need not be Borel-measurable. Lower semianalyticity makes it universally measurable, so that $\int J^*(x')\, t(dx' \mid x, u)$, and hence $T(J^*)$, is well defined.
-- source:
--   Bertsekas & Shreve, Stochastic Optimal Control: The Discrete-Time Case, Athena Scientific 1996, p. 221, Corollary 9.4.1

import Mathlib
import Definitions.Def_BertsekasShreve_BorelInfinite_Analytic
import Definitions.Def_BertsekasShreve_BorelInfinite_ExtArith
import Definitions.Def_BertsekasShreve_BorelInfinite_Model
import Definitions.Def_BertsekasShreve_BorelInfinite_Policy

open MeasureTheory ProbabilityTheory Filter Topology

namespace BertsekasShreve.BorelInfinite

/-- **Corollary 9.4.1** (p. 221). (P)(N)(D) The function `J* : S → R*` is lower semianalytic. -/
theorem Jstar_lowerSemianalytic {S C W : Type*}
    [TopologicalSpace S] [BertsekasShreve.AnalyticSelection.IsBorelSpace S] [MeasurableSpace S] [BorelSpace S] [Nonempty S]
    [TopologicalSpace C] [BertsekasShreve.AnalyticSelection.IsBorelSpace C] [MeasurableSpace C] [BorelSpace C] [Nonempty C]
    [TopologicalSpace W] [BertsekasShreve.AnalyticSelection.IsBorelSpace W] [MeasurableSpace W] [BorelSpace W] [Nonempty W]
    (M : Model S C W)
    (hcase : M.CaseP ∨ M.CaseN ∨ M.CaseD) :
    IsLowerSemianalyticFun M.Jstar := by sorry

end BertsekasShreve.BorelInfinite
