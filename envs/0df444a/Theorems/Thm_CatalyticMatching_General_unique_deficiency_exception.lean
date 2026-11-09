-- Prove2me | Theorems.Thm_CatalyticMatching_General_unique_deficiency_exception
-- name    : CatalyticMatching.General.unique_deficiency_exception
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:55:26.226201+00:00
-- url     : https://prove2.me/theorems/5b1538e6-60ec-4ad5-aa1f-90947588fc3b
-- title:
--   Lemma 3.6 (2B) — unique exceptional value for deficiency
-- statement:
--   Let $T'$ have rank $k$, with edge $e$ evaluated at $a_e$. Suppose $b\in\{1,\ldots,n^{10}\}$ leaves the rank equal to $k$, and fix any $u\in D(T'_{e\leftarrow b})\setminus D(T')$. Then
--
--   $$\forall c\in\mathbb Q\setminus\{a_e\},\quad u\in D(T'_{e\leftarrow c}).$$
--
--   The same chosen vertex persists under every stated rational replacement. This is the chosen-witness reading used in the proof on pages 12–13.
--
--   Differences from the source:
--   - encoding: arbitrary finite labelled graph or matrix → vertices and indices in Fin n, with arbitrary n; reason: relabeling covers every finite instance, including n=0 and n=1
--   - reading: the printed existential introduces u, then uses u in the conclusion without an explicit scope → universally bind any chosen newly deficient u before quantifying over every rational replacement; reason: the proof fixes an arbitrary such u on p.12 and establishes membership for that same u on p.13
-- source:
--   Srijan Chakraborty, Samir Datta, Aryan Kusre, Partha Mukhopadhyay, Amit Sinhababu, Maximum Matching and Related Problems in Catalytic Logspace, STOC 2027 submission #479 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/479.pdf, Lemma 3.6, printed p.12 = PDF p.12

import Definitions.Def_CatalyticMatching_General_Tutte

namespace CatalyticMatching.General

/-- Lemma 3.6 pp.12--13. Reading: the printed existential fixes any newly deficient u, as in its proof; the same u persists. -/
theorem unique_deficiency_exception {n : ℕ} (G : SimpleGraph (Fin n))
    (a : G.edgeSet → ℚ) (e : G.edgeSet) (b : ℚ) (hb : TestValue n b)
    (k : ℕ) (hbase : (tutteEval G a).rank = k)
    (hequal : (tutteEval G (perturb a e b)).rank = k)
    (u : Fin n) (hu : u ∈ deficiency (tutteEval G (perturb a e b)) \ deficiency (tutteEval G a)) :
    ∀ c : ℚ, c ≠ a e → u ∈ deficiency (tutteEval G (perturb a e c)) := by sorry

end CatalyticMatching.General
