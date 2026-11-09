-- Prove2me | Theorems.Thm_BipartiteVRM_Competitive_offline_attainment
-- name    : BipartiteVRM.Competitive.offline_attainment
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:07:09.429863+00:00
-- url     : https://prove2.me/theorems/79feafa1-f8e7-46a5-bd3e-7481322307e2
-- title:
--   §2 — the timed offline minimum and a TA minimizer exist
-- statement:
--   For every finite balanced input $I$ in any metric space, the offline objective (2.1) is finite and attained, and a TA-distance minimum perfect matching exists:
--
--   $$\exists M,t:\ C(M,t)=\mathrm{OPT},\qquad
--   \mathrm{OPT}\le C(N,u)\quad\text{for every feasible }(N,u),\qquad
--   \exists M^*:\ D(M^*)=\min_{N\text{ perfect}}D(N).$$
--
--   All displayed matchings are perfect and all match times are feasible. The value $\mathrm{OPT}$ is nonnegative. The empty input is permitted. This makes the real conversion of the independently defined timed infimum safe and provides the comparison matching needed in §4.2. It is an unnumbered well-posedness fact implicit in the source's minima, not a new numbered milestone.
--
--   Differences from the source:
--   - encoding: finite disjoint labeled sets R and S in any metric space → finite natural-number supports on the disjoint sum of two label types, Finset edges, and arbitrary MetricSpace X; reason: every finite labeled instance can be relabeled this way; labels give no future data and distinct items may coincide in space and time
--   - encoding: the minimum actual distance-plus-both-sides-delay objective OPT in (2.1) → the real projection of its ENNReal infimum over every perfect matching and feasible real match-time function; reason: offline_attainment and the main goal conclude finiteness and attainment, so the projection never substitutes a default for an infinite value
-- source:
--   Tung-Wei Kuo, STOC 2027 submission #528 (October 2026), p. 6, §2.1–§2.3, (2.1) and the minimum preceding Lemma 2.1

import Definitions.Def_BipartiteVRM_Competitive_Specifications

set_option autoImplicit false

namespace BipartiteVRM.Competitive

/-- §2.1–§2.3, p. 6: the actual timed offline minimization is finite and attained.
This justifies the real-valued OPT, independently of the TA-cost identity. -/
theorem offline_attainment {X : Type*} [MetricSpace X] (I : Input X) :
    OfflineAttained I ∧ ∃ Mstar, IsOptimal I Mstar := by sorry

end BipartiteVRM.Competitive
