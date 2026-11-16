-- Prove2me | Theorems.Thm_AMRangeAvoid_Characterization_Supplement_theorem_4_6
-- name    : AMRangeAvoid.Characterization.Supplement.theorem_4_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:29:44.853687+00:00
-- url     : https://prove2.me/theorems/bcd418a4-d4cf-4fb3-95f0-2e1e7099b6c1
-- title:
--   Theorem 4.6 — Complement GapSVP at the source approximation factor reduces to SSLB
-- statement:
--   For $n\ge2$ take $\gamma(n)=400\lceil\sqrt{n/\log_2 n}\rceil$, and put $\gamma(1)=400$. This factor has the source asymptotic order and gives a deterministic polynomial-time many-one reduction
--
--   $$\gamma(n)=\Theta\!\left(\sqrt{\frac n{\log_2 n}}\right),\qquad \overline{\mathrm{GapSVP}}_\gamma\le_m^{\mathrm P}\mathrm{SSLB}.$$
--
--   The input ranges over every positive dimension, every nonsingular rational basis and every positive rational threshold. YES means $\lambda_1(L(B))>\gamma(n)d$, while NO means $\lambda_1(L(B))\le d$. There is no integrality, fixed-dimension or threshold-normalization restriction.
--
--   Differences from the source:
--   - encoding: the existential factor realized in the proof as 400 ceil(sqrt(n/log₂ n)) → that proof factor for n at least two, with value 400 in dimension one and uniform positive Theta constants; reason: the printed quotient is undefined at n=1; exact one-dimensional comparison retains those instances without changing the positive-dimensional problem or the asymptotic factor
--   - encoding: shortest nonzero length compared with d or gamma d → existential short-vector and universal strict long-vector predicates in EuclideanSpace; reason: positive dimension and nonsingularity ensure the minimum is attained, so these are equivalent comparisons without default-valued infima
-- source:
--   Zeyong Li, STOC 2027 submission #502 (October 2026), Theorem 4.6, printed p.21 (PDF p.23); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/502.pdf

import Definitions.Def_AMRangeAvoid_Characterization_Supplement_Lattices
import Definitions.Def_AMRangeAvoid_Characterization_SSLB

namespace AMRangeAvoid.Characterization.Supplement

theorem theorem_4_6 :
    SqrtTheta gamma ∧ PromiseReduces (CoGapSVP gamma) SSLB := by sorry

end AMRangeAvoid.Characterization.Supplement
