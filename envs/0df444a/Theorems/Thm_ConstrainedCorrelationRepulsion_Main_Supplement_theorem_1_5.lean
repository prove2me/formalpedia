-- Prove2me | Theorems.Thm_ConstrainedCorrelationRepulsion_Main_Supplement_theorem_1_5
-- name    : ConstrainedCorrelationRepulsion.Main.Supplement.theorem_1_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:07:49.384772+00:00
-- url     : https://prove2.me/theorems/20a661b6-2963-433c-b247-78f17e346885
-- title:
--   Theorem 1.5 — must-link-only randomized (1.3865 + ε) approximation
-- statement:
--   For every fixed real $\varepsilon>0$, there is one finite randomized program running in polynomial time on every feasible complete unweighted instance $I$ with must-links only. Every supported output $P$ satisfies all must-links and
--
--   $$\mathbb E[\operatorname{cost}_I(P)]\le\left(\frac{2773}{2000}+\varepsilon\right)\operatorname{OPT}(I).$$
--
--   The vertex count, signs and must-link components are unrestricted, including empty and singleton inputs. The polynomial constants and program may depend on $\varepsilon$ and are chosen before all inputs. This is unconditional algorithm existence; it assumes no unconstrained approximation algorithm as a hypothesis. The existing true-twin and expansion constructions preserve empty $H$, allowing the cited unconstrained algorithm to be used with accuracy $\varepsilon/2$ and transfer slack $\varepsilon/2$.
--
--   Differences from the source:
--   - encoding: randomized polynomial-time (1.3865 + ε)-approximation with must-links only → uniform published fair-coin bit-cost program guarantee on H-empty inputs, with 1.3865 = 2773/2000 exactly; reason: this states the same expected objective ratio and hard feasibility on every output; padding max(2,n) includes empty and singleton inputs
-- source:
--   Yixin Cao, Ying Xu, STOC 2027 submission #869 (October 2026), Theorem 1.5, printed p.16 (PDF p.17), also announced printed p.2 (PDF p.3)

import Definitions.Def_ConstrainedCorrelationRepulsion_Main_Supplement_MustLinks

namespace ConstrainedCorrelationRepulsion.Main.Supplement

/-- Theorem 1.5, printed p.16 / PDF p.17: the final unconditional existence result,
not a transfer theorem with the external unconstrained algorithm assumed. -/
theorem theorem_1_5 (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    MustLinkApproximation ((2773 : ℝ)/2000 + epsilon) := by sorry

end ConstrainedCorrelationRepulsion.Main.Supplement
