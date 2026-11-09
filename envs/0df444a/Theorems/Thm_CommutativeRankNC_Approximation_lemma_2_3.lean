-- Prove2me | Theorems.Thm_CommutativeRankNC_Approximation_lemma_2_3
-- name    : CommutativeRankNC.Approximation.lemma_2_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:49:32.618584+00:00
-- url     : https://prove2.me/theorems/dff7ce24-b474-42fb-ad0b-d265670329f5
-- title:
--   Lemma 2.3 — Joint uniformity of polynomial evaluations
-- statement:
--   Let $m\ge2$, $t\ge1$, and let $\alpha_1,\ldots,\alpha_m$ be any distinct points of the constructed field $\mathbb F_q$. Choose the $t$ coefficients of $p_a(Z)=\sum_{j<t}a_jZ^j$ uniformly and independently in $\mathbb F_q$. For every $s\le t$, every injection selecting $s$ indices, and every field-value pattern $(y_1,\ldots,y_s)$,
--
--   $$\Pr[p_a(\alpha_{i_j})=y_j\text{ for all }j]=q^{-s}.$$
--
--   This includes the empty selection and $t>m$ with the at-most-$t$ convention. The formula is the full joint uniform law, rather than only pairwise independence.
--
--   Differences from the source:
--   - encoding: elements of the quotient field F₂[z]/(f) → binary coefficient representatives, finite trial division, and reduction modulo the first irreducible polynomial; reason: these are the explicit field representation and deterministic search in the proof of Lemma 2.1; no arithmetic oracle is used
--   - encoding: joint evaluations of a uniform coefficient tuple in F_q^t → the number of base-q seeds giving the prescribed field-value pattern divided by q^t; reason: the q^t seeds enumerate all coefficient tuples once; normalized fiber counts give the same joint law
--   - encoding: one-based matrix and variable indices → zero-based finite index types and ordered pairs for truncated blocks; reason: the same entries and blocks are present under a bijective reindexing
-- source:
--   Foram Lakhani, Partha Mukhopadhyay, STOC 2027 submission #458 (October 2026), Lemma 2.3, PDF/printed p.10; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/458.pdf

import Definitions.Def_CommutativeRankNC_Approximation_Signs

namespace CommutativeRankNC.Approximation

/-- Lemma 2.3, PDF/printed p.10: joint uniformity for every at-most-t distinct
evaluation points, including t greater than the number of points. -/
theorem lemma_2_3 (m t : ℕ) (hm : 2 ≤ m) (ht : 0 < t)
    (α : Fin m ↪ Fin (fieldCard m)) :
    ∀ s : ℕ, s ≤ t → ∀ (I : Fin s ↪ Fin m) (y : Fin s → Fin (fieldCard m)),
      (((Finset.range (seedCard m t)).filter (fun a =>
        ∀ j, seedEvaluation m t a (α (I j)).val = (y j).val)).card : ℝ) /
          (seedCard m t : ℝ) = (fieldCard m : ℝ) ^ (-(s : ℤ)) := by sorry

end CommutativeRankNC.Approximation
