-- Prove2me | Theorems.Thm_AGT_ic_implies_wmon
-- name    : AGT.ic_implies_wmon
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-13T03:08:46.682746+00:00
-- url     : https://prove2.me/theorems/63a77a31-7c31-453d-80a1-ff8eb2143077
-- title:
--   Incentive compatibility forces weak monotonicity
-- statement:
--   Incentive compatibility forces weak monotonicity of the choice rule (Theorem 9.29 of *Algorithmic Game Theory*, necessity half). If some payment functions make $(f, p)$ incentive compatible on the domain $V$, then $f$ satisfies WMON: whenever a unilateral change of player $i$'s valuation from $v_i$ to $v_i'$ moves the outcome from $a$ to $b \ne a$, we have $v_i'(b) - v_i'(a) \ge v_i(b) - v_i(a)$.
--
--   *A note on the rendering.* This half of Theorem 9.29 carries no hypotheses beyond incentive compatibility itself — no convexity, no finiteness, arbitrary domains; the book's proof is two applications of the truthfulness inequality. The sufficiency half, which does need convex domains, is the separate milestone `wmon_implies_ic_convex`; splitting the two keeps this direction at its full strength.
-- source:
--   N. Nisan, T. Roughgarden, E. Tardos, V. V. Vazirani (eds.), Algorithmic Game Theory, Cambridge University Press 2007, https://doi.org/10.1017/CBO9780511800481, Section 9.5.3, Theorem 9.29 (necessity), pp. 226-227

import Definitions.Def_agt_mechanism

namespace AGT

/-- Incentive compatibility forces weak monotonicity of the choice rule
(Theorem 9.29 of *Algorithmic Game Theory*, necessity half): if some
payments make `f` incentive compatible, then whenever a unilateral change
of valuation moves the outcome from `a` to `b`, the deviator raised the
value of `b` relative to `a`.  This half needs no structure whatsoever on
the domains. -/
theorem ic_implies_wmon {A ι : Type*} [Fintype ι] [DecidableEq ι]
    (V : ι → Set (A → ℝ)) (f : (ι → A → ℝ) → A)
    (p : ι → (ι → A → ℝ) → ℝ) (hic : MechIncentiveCompatible V f p) :
    WeakMonotone V f := by
  sorry

end AGT
