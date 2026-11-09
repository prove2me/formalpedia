-- Prove2me | Theorems.Thm_CatalyticMatching_General_rank_or_deficiency_improvement
-- name    : CatalyticMatching.General.rank_or_deficiency_improvement
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:54:43.980052+00:00
-- url     : https://prove2.me/theorems/c9dd65ee-0c10-4f41-ac92-18b89595a5f8
-- title:
--   Theorem 3.2 — Geelen rank-or-deficiency improvement
-- statement:
--   Let $G$ be any finite simple graph on $n$ vertices, $T$ its generic Tutte matrix, and $T'$ an arbitrary rational evaluation. Write $D(B)$ for rank deficiency and $D(G)$ for vertices missed by some maximum matching. Then
--
--   $$\bigl(\operatorname{rank}T'=\operatorname{rank}T\ \land\ D(T')=D(T)=D(G)\bigr)\ \lor\ \exists e\in E,\ a\in[n^{10}]:\operatorname{rank}T'_{e\leftarrow a}=\operatorname{rank}T'+2$$
--   $$\lor\ \exists e\in E,\ a\in[n^{10}]:\operatorname{rank}T'_{e\leftarrow a}=\operatorname{rank}T'\ \land\ D(T')\subsetneq D(T'_{e\leftarrow a}).$$
--
--   In the existential displays $e$ ranges over edges and $a$ over the stated integer interval, embedded in the rationals. This retains both possible forms of improvement and the whole terminal equality.
--
--   Differences from the source:
--   - encoding: arbitrary finite labelled graph or matrix → vertices and indices in Fin n, with arbitrary n; reason: relabeling covers every finite instance, including n=0 and n=1
-- source:
--   Srijan Chakraborty, Samir Datta, Aryan Kusre, Partha Mukhopadhyay, Amit Sinhababu, Maximum Matching and Related Problems in Catalytic Logspace, STOC 2027 submission #479 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/479.pdf, Theorem 3.2, printed p.11 = PDF p.11

import Definitions.Def_CatalyticMatching_General_Tutte

namespace CatalyticMatching.General

/-- Theorem 3.2 p.11, arbitrary rational evaluation, witness range [n^10]. -/
theorem rank_or_deficiency_improvement {n : ℕ} (G : SimpleGraph (Fin n))
    (a : G.edgeSet → ℚ) :
    ((tutteEval G a).rank = (genericTutte G).rank ∧
      deficiency (tutteEval G a) = deficiency (genericTutte G) ∧
      deficiency (genericTutte G) = graphDeficiency G) ∨
    (∃ (e : G.edgeSet) (b : ℚ), TestValue n b ∧
      (tutteEval G (perturb a e b)).rank = (tutteEval G a).rank + 2) ∨
    (∃ (e : G.edgeSet) (b : ℚ), TestValue n b ∧
      (tutteEval G (perturb a e b)).rank = (tutteEval G a).rank ∧
      deficiency (tutteEval G a) ⊂ deficiency (tutteEval G (perturb a e b))) := by sorry

end CatalyticMatching.General
