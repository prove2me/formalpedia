-- Prove2me | Theorems.Thm_BuchiRabinIndex_LowerBound_lemma_18
-- name    : BuchiRabinIndex.LowerBound.lemma_18
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T06:31:50.003214+00:00
-- url     : https://prove2.me/theorems/689a45b8-81e3-4734-929f-e3165afa542d
-- title:
--   Lemma 18 — chain preservation
-- statement:
--   Let $n\ge2$ and let $x\ne y$ lie in $T^{(n)}$, at possibly different weights. For $i=1,2$, if both lie in $T_i$, then
--   $$|C(x)\cup C(y)|=|C(\phi_i x)\cup C(\phi_i y)|+1.$$
--   If the nodes lie in different parts, in either order, then
--   $$C(x)\cap C(y)=\{\epsilon,1\},\qquad |C(x)\cup C(y)|=\operatorname{weight}(x)+\operatorname{weight}(y).$$
--   In particular the union has size $2w$ if both weights equal $w$.
--
--   The chains are tree independent; their subscripts in the source indicate ambient full trees only.
--
--   Differences from the source:
--   - encoding: nodes are finite words of positive integers → List Nat with positivity in node and tree predicates; reason: children retain the source’s indices starting at 1
--   - encoding: the unique n-full ordered tree of Definition 12 → the explicitly enumerated positive words of weight at most n−1; reason: this is the same finite tree; no size is fixed
-- source:
--   Cong Tian, Runzhe Ma, Wensheng Wang, Zhenhua Duan, Büchi Determinization with Optimal States and Square Root Index Improvement, STOC 2027 submission #1731 (October 2026), Lemma 18, p. 14; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1731.pdf

import Definitions.Def_BuchiRabinIndex_LowerBound_Nodes

set_option autoImplicit false

namespace BuchiRabinIndex.LowerBound

/-- STOC 2027 submission #1731, lemma 18; statement only. -/
theorem lemma_18 (n : ℕ) (hn : 2 ≤ n) (x y : Node)
    (hx : x ∈ fullTree n) (hy : y ∈ fullTree n) (hne : x ≠ y) :
    (x ∈ part1 n → y ∈ part1 n →
      (chain x ∪ chain y).card = (chain (phi1 x) ∪ chain (phi1 y)).card + 1) ∧
    (x ∈ part2 n → y ∈ part2 n →
      (chain x ∪ chain y).card = (chain (phi2 x) ∪ chain (phi2 y)).card + 1) ∧
    ((x ∈ part1 n ∧ y ∈ part2 n) ∨ (x ∈ part2 n ∧ y ∈ part1 n) →
      chain x ∩ chain y = {[], [1]} ∧
      (chain x ∪ chain y).card = weight x + weight y ∧
      ∀ w, weight x = w → weight y = w → (chain x ∪ chain y).card = 2 * w) := by sorry

end BuchiRabinIndex.LowerBound
