-- Prove2me | Theorems.Thm_ChvatalOneHard398_SAT_Supplement_lemma_4
-- name    : ChvatalOneHard398.SAT.Supplement.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:22:32.620524+00:00
-- url     : https://prove2.me/theorems/0a030c1a-d5fb-4db8-9863-9a537a14b75b
-- title:
--   Lemma 4 — dual bases and widths
-- statement:
--   Let $B\in\mathbb Q^{d\times d}$ be nonsingular, let $L=B\mathbb Z^d$, let $t\in\mathbb Q^d$, and let $r>0$ be real. If $w_1,\ldots,w_d$ form a basis of $L^*$, their transposes multiplied by $B$ are the rows of an integer unimodular matrix. Conversely every integer unimodular matrix arises this way from a dual basis. For every real vector $w$,
--   $$\operatorname{width}_{Q(B,t,r)}(B^Tw)=2r\sum_i|w_i|.$$
--
--   The correspondence and exact width identity connect arbitrary unimodular directions to dual bases. The radius in this lemma need not be rational.
--
--   Differences from the source:
--   - encoding: Euclidean vectors and column lattice bases → Fin d coordinates and column-generated EuclideanSpace lattices; reason: the finite coordinates and Euclidean norm represent the same vectors and bases
--   - encoding: support-function widths, with empty sets handled separately → EReal support values for nonempty sets and width zero for the empty set; reason: unbounded widths stay infinite and every empty-set conclusion is retained
-- source:
--   Alberto Del Pia, 0/1 integer programming over polytopes of Chvátal rank one is as hard as lattice problems, STOC 2027 submission #398 (October 2026), p.10, Lemma 4. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/398.pdf

import Mathlib
import Definitions.Def_ChvatalOneHard398_SAT_Supplement_Probability

namespace ChvatalOneHard398.SAT.Supplement
open scoped BigOperators
open CombOpt.ChvatalRank

theorem lemma_4 {d : ℕ} (B : Matrix (Fin d) (Fin d) ℚ)
    (t : Fin d → ℚ) (r : ℝ) (hB : B.det ≠ 0) (hr : 0 < r)
    (W : Matrix (Fin d) (Fin d) ℝ) (hW : dualBasis (qLattice B) W) :
    (∃ U : Matrix (Fin d) (Fin d) ℤ, unimodular U ∧
      ∀ i j, (U i j : ℝ) = ∑ l, W l i*(B l j : ℝ)) ∧
    (∀ U : Matrix (Fin d) (Fin d) ℤ, unimodular U →
      ∃ V : Matrix (Fin d) (Fin d) ℝ, dualBasis (qLattice B) V ∧
        ∀ i j, (U i j : ℝ) = ∑ l, V l i*(B l j : ℝ)) ∧
    (∀ w : Fin d → ℝ, width (parallelepiped B t r)
      (fun j => ∑ l, (B l j : ℝ)*w l) = ((2*r*oneNorm w : ℝ) : EReal)) := by sorry

end ChvatalOneHard398.SAT.Supplement
