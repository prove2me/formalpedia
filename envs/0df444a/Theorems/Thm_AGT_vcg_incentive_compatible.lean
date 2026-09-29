-- Prove2me | Theorems.Thm_AGT_vcg_incentive_compatible
-- name    : AGT.vcg_incentive_compatible
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-13T03:08:19.425708+00:00
-- url     : https://prove2.me/theorems/890a7919-c3e3-4c80-b5af-8618b32ef86f
-- title:
--   VCG mechanisms are incentive compatible
-- statement:
--   Every Vickrey–Clarke–Groves mechanism is incentive compatible (Theorem 9.17 of *Algorithmic Game Theory*). If the choice rule maximizes social welfare $\sum_i v_i(a)$ over the domain and payments have the Groves form $p_i = h_i(v_{-i}) - \sum_{j \ne i} v_j(f(v))$, then for every player, every valuation profile from the domain, and every unilateral misreport from the domain, truth-telling yields at least the misreport's quasilinear utility.
--
--   *A note on the rendering.* No structure on the domains $V_i$ is required — any sets of valuations work. "$h_i$ does not depend on $v_i$" is rendered as invariance of $h_i$ under updating coordinate $i$, the standard formal reading; the payments identity is required only on profiles from the domain.
-- source:
--   N. Nisan, T. Roughgarden, E. Tardos, V. V. Vazirani (eds.), Algorithmic Game Theory, Cambridge University Press 2007, https://doi.org/10.1017/CBO9780511800481, Section 9.3.3, Theorem 9.17, p. 218

import Definitions.Def_agt_mechanism

namespace AGT

/-- Every Vickrey–Clarke–Groves mechanism is incentive compatible (Theorem
9.17 of *Algorithmic Game Theory*).  The Groves payment aligns each
player's quasilinear utility with the social welfare, which the choice rule
maximizes, so truth-telling is a dominant strategy whatever the others
report.  No structure on the domains `V i` is needed. -/
theorem vcg_incentive_compatible {A ι : Type*} [Fintype ι] [DecidableEq ι]
    (V : ι → Set (A → ℝ)) (f : (ι → A → ℝ) → A)
    (p : ι → (ι → A → ℝ) → ℝ) (hvcg : IsVCG V f p) :
    MechIncentiveCompatible V f p := by
  sorry

end AGT
