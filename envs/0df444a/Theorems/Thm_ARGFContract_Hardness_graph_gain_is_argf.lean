-- Prove2me | Theorems.Thm_ARGFContract_Hardness_graph_gain_is_argf
-- name    : ARGFContract.Hardness.graph_gain_is_argf
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:47:01.637342+00:00
-- url     : https://prove2.me/theorems/5cada563-b0dd-40aa-ac88-b086128ce569
-- title:
--   Proof of Theorem 1, pp. 8–9 — mathematical ARGF properties (1),(2),(4),(5); oracle property (3) is companion reduction_polytime
-- statement:
--   Let $G$ be a finite simple graph on $n\ge1$ vertices. For $p_i=(n-i)/(2n^2)$, $\varepsilon_n=1/(4n^2)$ and $f_G(S)=\sum_{i\in S}p_i+\varepsilon_nh_G(S)$,
--
--   $$f_G\in\mathrm{ARGF}(p).$$
--
--   This item states anchoring, the full range $[0,1]$, subadditivity for arbitrary overlapping sets, and competency dominance including equal agent labels. The oracle property (3) is the companion milestone `ARGFContract.Hardness.reduction_polytime`; the two targets together give all five items of Definition 2.1.
--
--   Differences from the source:
--   - encoding: vertices labelled 1 through n and real expressions in the rational construction → Fin n labels and exact rational expressions, cast to reals when needed; reason: the label bijection sends i to i+1 and rational values embed exactly into the reals
--   - encoding: ARGF includes polynomial oracle property (3) → this item states (1),(2),(4),(5), with (3) stated by companion reduction_polytime; reason: mathematical properties and uniform computation have separate interfaces; both are target milestones and the goal includes all five
-- source:
--   Jalal Etesami, Larkin Liu, Rilind Sahitaj, Optimal Contract Design for Rank Ordered Gain Functions with Modular Costs, STOC 2027 submission #348 (October 2026), proof of Theorem 1, equation (3.1), items (i),(ii),(iv),(v), pp. 8–9; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/348.pdf

import Definitions.Def_ARGFContract_Hardness_RankConstruction

namespace ARGFContract.Hardness

/-- Proof of Theorem 1, pp. 8–9, items (i),(ii),(iv),(v). Item (iii) is M4. -/
theorem graph_gain_is_argf {n : ℕ} (hn : 0 < n) (G : SimpleGraph (Fin n)) :
    IsARGF (fun i => (rankCompetency i : ℝ)) (fun S => (graphGain G S : ℝ)) := by sorry

end ARGFContract.Hardness
