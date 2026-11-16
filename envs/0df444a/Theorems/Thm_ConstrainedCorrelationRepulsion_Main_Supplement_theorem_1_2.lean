-- Prove2me | Theorems.Thm_ConstrainedCorrelationRepulsion_Main_Supplement_theorem_1_2
-- name    : ConstrainedCorrelationRepulsion.Main.Supplement.theorem_1_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:05:35.036137+00:00
-- url     : https://prove2.me/theorems/331592b8-5708-4ed7-b560-679ccc4470c5
-- title:
--   Theorem 1.2 — both constrained-clustering hardness thresholds
-- statement:
--   For every fixed real $\varepsilon>0$, constrained correlation clustering is NP-hard to approximate within $\sqrt2-\varepsilon$, and assuming the Unique Games Conjecture it is NP-hard to approximate within $2-\varepsilon$:
--
--   $$\operatorname{Hard}(\sqrt2-\varepsilon)\ \land\ \bigl(\mathrm{UGC}\Rightarrow\operatorname{Hard}(2-\varepsilon)\bigr).$$
--
--   Here hardness means actual polynomial-time reductions from every NP language to explicit feasible minimization gaps. Both clauses already hold on the cluster-deletion subclass $M=\varnothing$, $H=E^-$. Requested factors at or below one retain the monotone approximation-task meaning using a harder, nonoverlapping gap; no upper bound on $\varepsilon$ is imposed. The cited external vertex-cover hardness results are proof dependencies and are not additional hypotheses of this theorem. This supplies the hardness side of the paper's approximation threshold.
--
--   Differences from the source:
--   - encoding: NP-hardness within each stated factor → explicit polynomial reductions to a fixed harder separated gap on the cluster-deletion subclass; reason: the source proves hardness on this subclass; choosing an intermediate factor and monotonicity covers every positive accuracy without overlapping promise sets
-- source:
--   Yixin Cao, Ying Xu, STOC 2027 submission #869 (October 2026), Theorem 1.2, printed p.1 (PDF p.2), repeated statement and proof printed p.37 (PDF p.38)

import Definitions.Def_ConstrainedCorrelationRepulsion_Main_Supplement_Hardness

namespace ConstrainedCorrelationRepulsion.Main.Supplement

/-- Both clauses of Theorem 1.2. External vertex-cover hardness results are proof
dependencies, never extra hypotheses. The reductions already land in cluster deletion. -/
theorem theorem_1_2 (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ApproximationNPHard (Real.sqrt 2 - epsilon) ∧
    (OptInapprox.MaxCut.UGC → ApproximationNPHard (2 - epsilon)) := by sorry

end ConstrainedCorrelationRepulsion.Main.Supplement
