-- Prove2me | Theorems.Thm_CatalyticMatching_General_unique_rank_exception
-- name    : CatalyticMatching.General.unique_rank_exception
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:54:22.734937+00:00
-- url     : https://prove2.me/theorems/1a47e0d0-6e86-4a69-98e1-7ff749a2bd59
-- title:
--   Lemma 3.5 (2A) — unique exceptional value for rank increase
-- statement:
--   Let $T'$ be a rational evaluation, let $e$ be an edge with current value $a_e$, and suppose some $b\in\{1,\ldots,n^{10}\}$ satisfies $\operatorname{rank}T'_{e\leftarrow b}=\operatorname{rank}T'+2$. Then
--
--   $$\forall c\in\mathbb Q\setminus\{a_e\},\quad\operatorname{rank}T'_{e\leftarrow c}=\operatorname{rank}T'+2.$$
--
--   The conclusion covers all rational replacements, and changing one edge updates both skew entries. This identifies the exceptional value without a finite-range restriction on the conclusion.
--
--   Differences from the source:
--   - encoding: arbitrary finite labelled graph or matrix → vertices and indices in Fin n, with arbitrary n; reason: relabeling covers every finite instance, including n=0 and n=1
-- source:
--   Srijan Chakraborty, Samir Datta, Aryan Kusre, Partha Mukhopadhyay, Amit Sinhababu, Maximum Matching and Related Problems in Catalytic Logspace, STOC 2027 submission #479 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/479.pdf, Lemma 3.5, printed p.12 = PDF p.12

import Definitions.Def_CatalyticMatching_General_Tutte

namespace CatalyticMatching.General

/-- Lemma 3.5 p.12. The universal perturbation is over all rationals, not just the finite witness range. -/
theorem unique_rank_exception {n : ℕ} (G : SimpleGraph (Fin n))
    (a : G.edgeSet → ℚ) (e : G.edgeSet) (b : ℚ) (hb : TestValue n b)
    (hinc : (tutteEval G (perturb a e b)).rank = (tutteEval G a).rank + 2) :
    ∀ c : ℚ, c ≠ a e →
      (tutteEval G (perturb a e c)).rank = (tutteEval G a).rank + 2 := by sorry

end CatalyticMatching.General
