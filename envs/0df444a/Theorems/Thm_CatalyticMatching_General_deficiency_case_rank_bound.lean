-- Prove2me | Theorems.Thm_CatalyticMatching_General_deficiency_case_rank_bound
-- name    : CatalyticMatching.General.deficiency_case_rank_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:55:24.032389+00:00
-- url     : https://prove2.me/theorems/c1f50ccb-372c-4329-9bf4-c1a6c81b3261
-- title:
--   Claim 3.7 — no rank increase in the deficiency case
-- statement:
--   Use the complete setup of Lemma 3.6: $T'$ has rank $k$, edge $e$ has value $a_e$, some $b\in\{1,\ldots,n^{10}\}$ leaves rank equal to $k$, and a chosen vertex $u$ belongs to $D(T'_{e\leftarrow b})\setminus D(T')$. Then
--
--   $$\forall c\in\mathbb Q\setminus\{a_e\},\quad\operatorname{rank}T'_{e\leftarrow c}\le k.$$
--
--   This is the claim inside the deficiency lemma's proof, with its inherited context made explicit.
--
--   Differences from the source:
--   - encoding: arbitrary finite labelled graph or matrix → vertices and indices in Fin n, with arbitrary n; reason: relabeling covers every finite instance, including n=0 and n=1
--   - encoding: Claim 3.7 inside the proof of Lemma 3.6 → all enclosing data and hypotheses are explicit binders; reason: a standalone item must carry the complete inherited setup
-- source:
--   Srijan Chakraborty, Samir Datta, Aryan Kusre, Partha Mukhopadhyay, Amit Sinhababu, Maximum Matching and Related Problems in Catalytic Logspace, STOC 2027 submission #479 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/479.pdf, Claim 3.7, printed p.12 = PDF p.12

import Definitions.Def_CatalyticMatching_General_Tutte

namespace CatalyticMatching.General

/-- Claim 3.7 p.12 with the complete enclosing Lemma 3.6 setup, including the chosen newly deficient vertex. -/
theorem deficiency_case_rank_bound {n : ℕ} (G : SimpleGraph (Fin n))
    (a : G.edgeSet → ℚ) (e : G.edgeSet) (b : ℚ) (hb : TestValue n b)
    (k : ℕ) (hbase : (tutteEval G a).rank = k)
    (hequal : (tutteEval G (perturb a e b)).rank = k)
    (u : Fin n) (hu : u ∈ deficiency (tutteEval G (perturb a e b)) \ deficiency (tutteEval G a)) :
    ∀ c : ℚ, c ≠ a e → (tutteEval G (perturb a e c)).rank ≤ k := by sorry

end CatalyticMatching.General
