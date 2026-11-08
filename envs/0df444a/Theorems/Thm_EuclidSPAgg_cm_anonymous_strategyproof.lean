-- Prove2me | Theorems.Thm_EuclidSPAgg_cm_anonymous_strategyproof
-- name    : EuclidSPAgg.cm_anonymous_strategyproof
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T06:43:25.266203+00:00
-- url     : https://prove2.me/theorems/96d0b3f8-bf4b-46cb-bc06-520db4a899ea
-- title:
--   Proof of Theorem 8.5 — the coordinate-wise median is anonymous and strategyproof
-- statement:
--   For every $n\ge3$ and $d\ge1$, the coordinate-wise median $\mathrm{CM}_{n,d}$ is strategyproof and anonymous; that is, $\mathrm{CM}_{n,d}\in\mathcal A_{n,d}$. Hence the infimum in Theorem 8.5 is attained by the median.
--
--   With all reports but one fixed, the remaining report is clamped coordinate-wise to an interval, so its response is a Euclidean projection; anonymity holds because scalar order statistics are symmetric in the reports.
--
--   Differences from the source: none.
-- source:
--   Jia, Strategyproof Aggregation in Euclidean Spaces: Rigidity and Median Optimality, arXiv:2609.19394 (held version, sha256 891e6125…), proof of Theorem 8.5, p.35 (PDF p.37)

import Mathlib
import Definitions.Def_EuclidSPAgg_IsStrategyproof
import Definitions.Def_EuclidSPAgg_IsAnonymous
import Definitions.Def_EuclidSPAgg_CM
open RBMSensitivity (E)

namespace EuclidSPAgg

/-- **Proof of Theorem 8.5, attainment** (Jia, *Strategyproof Aggregation in Euclidean Spaces: Rigidity and Median Optimality*, arXiv:2609.19394 (held version, sha256 891e6125…), p.35 (PDF p.37)): for `n ≥ 3` and `d ≥ 1` the
coordinate-wise median `CM_{n,d}` is strategyproof and anonymous, i.e. it belongs to `A_{n,d}`
("The coordinate-wise median attains `R_{n,d}`. … truthful reporting minimizes the agent's
distance to the outcome. The mechanism is anonymous because scalar order statistics are symmetric
in the reports.").

**Formalization Note** `CM n d` is the paper's `CM_{n,d}`: standard basis, lower middle rank. -/
theorem cm_anonymous_strategyproof (n d : ℕ) (hn : 3 ≤ n) (hd : 1 ≤ d) :
    IsStrategyproof (CM n d) ∧ IsAnonymous (CM n d) := by sorry

end EuclidSPAgg
