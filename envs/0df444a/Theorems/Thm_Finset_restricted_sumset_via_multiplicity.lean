-- Prove2me | Theorems.Thm_Finset_restricted_sumset_via_multiplicity
-- name    : Finset.restricted_sumset_via_multiplicity
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-17T06:31:18.564365+00:00
-- url     : https://prove2.me/theorems/b383fead-3c72-48d0-9ce0-e90cd0f7ba23
-- title:
--   Small triple-representation set bounds the sumset via multiplicity
-- statement:
--   Let $G$ be an additive commutative group and let $A, B, S \subseteq G$ be finite sets, and let $M : \mathbb{N}$. Suppose every sum $a + b$ with $a \in A$ and $b \in B$ admits at least $M$ representations
--   $$a + b = s_1 - s_2 + s_3, \qquad (s_1, s_2, s_3) \in S \times S \times S.$$
--   Then
--   $$M \cdot |A + B| \le |S|^3.$$
--
--   The proof is double counting: the fibres of the map $S \times S \times S \to G$, $(s_1,s_2,s_3) \mapsto s_1 - s_2 + s_3$, over distinct sums $a+b \in A+B$ are pairwise disjoint and each has size at least $M$, while they all sit inside $S \times S \times S$, which has $|S|^3$ elements.
--
--   Note that $S \times S \times S$ is the Cartesian cube of $S$, and the image of the map above is the triple-representation set $S - S + S$. Neither is a dilate of $S$: no scaling is applied to $S$, and the three coordinates range independently.
--
--   In the Balog-Szemeredi-Gowers project this is the final counting step: the Tao-Vu injection supplies a uniform multiplicity $M$ of such triple representations for every sum in $A' + B'$, and this lemma converts that into the honest sumset bound $|A' + B'| \le |S|^3/M$.
-- source:
--   Double-counting step inside Fox-Sudakov, Dependent random choice, Random Structures & Algorithms 38 (2011) 68-99, Section 5.1 (p. 9) / the proof of Tao-Vu, Additive Combinatorics, Cambridge Univ. Press (2006), Theorem 2.29. Not separately stated in the cited works. Formalized in https://github.com/mysticflounder/lean-formalizations/blob/dd46c17a2a034d7bfa0df02e7f77834d35592864/lean/LeanFormalizations/Combinatorics/Additive/BalogSzemerediGowers.lean#L504-L590

import Mathlib

open scoped Pointwise

theorem Finset.restricted_sumset_via_multiplicity {G : Type*} [AddCommGroup G] [DecidableEq G]
    (A B S : Finset G) (M : ℕ) :
    (∀ a ∈ A, ∀ b ∈ B,
        M ≤ ((S ×ˢ S ×ˢ S).filter
          (fun p : G × G × G ↦ p.1 - p.2.1 + p.2.2 = a + b)).card) →
    M * (A + B).card ≤ S.card ^ 3 := by sorry
