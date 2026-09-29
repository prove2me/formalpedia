-- Prove2me | Theorems.Thm_Finset_sum_addConvolution_eq_card_product
-- name    : Finset.sum_addConvolution_eq_card_product
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-17T06:31:28.681281+00:00
-- url     : https://prove2.me/theorems/95ca6b9d-2218-4af4-9757-3de3f78b9d18
-- title:
--   Total mass of the additive convolution is $|X||Y|$
-- statement:
--   Let $G$ be an additive commutative group and let $X, Y \subseteq G$ be finite sets. With $r_{X,Y}(s) = X.\mathrm{addConvolution}\, Y\, s$ the number of representations $s = x + y$ with $x \in X$ and $y \in Y$, one has
--   $$\sum_{s \in X + Y} r_{X,Y}(s) = |X|\,|Y|.$$
--   Every pair $(x,y) \in X \times Y$ contributes exactly one to the fibre over its sum $x + y$, and every such sum lies in $X + Y$, so the fibres of $(x,y) \mapsto x+y$ partition $X \times Y$.
--
--   This elementary total-mass identity underpins the energy-to-graph step in two places. It bounds the contribution of the unpopular fibres to the energy, so that large energy forces many popular pairs. And it bounds the number of popular sums by a threshold (Markov) argument: if $S \subseteq X + Y$ and every $s \in S$ has $r_{X,Y}(s) \ge \theta$, then
--   $$\theta\,|S| \ \le\ \sum_{s \in S} r_{X,Y}(s) \ \le\ \sum_{s \in X+Y} r_{X,Y}(s) \ =\ |X|\,|Y|,$$
--   so $|S| \le |X||Y|/\theta$. That second bound is total mass plus a threshold, with no Cauchy-Schwarz step.
-- source:
--   Elementary total-mass identity sum_s r(s) = |X||Y| for the additive convolution; used inside the proof of Tao-Vu, Additive Combinatorics, Cambridge Univ. Press (2006), Lemma 2.30 (p. 80). Not separately stated in the cited works. Formalized in https://github.com/mysticflounder/lean-formalizations/blob/dd46c17a2a034d7bfa0df02e7f77834d35592864/lean/LeanFormalizations/Combinatorics/Additive/BalogSzemerediGowers.lean#L39-L52

import Mathlib

open scoped Pointwise

theorem Finset.sum_addConvolution_eq_card_product {G : Type*} [AddCommGroup G] [DecidableEq G]
    (X Y : Finset G) :
    ∑ s ∈ X + Y, X.addConvolution Y s = X.card * Y.card := by sorry
