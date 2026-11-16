-- Prove2me | Theorems.Thm_BuchiRabinIndex_LowerBound_Supplement_lemma_14
-- name    : BuchiRabinIndex.LowerBound.Supplement.lemma_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T13:51:30.799601+00:00
-- url     : https://prove2.me/theorems/d074fcae-5618-4114-8e9a-6a0ad8d85aef
-- title:
--   Lemma 14 — Coexistence is exactly the chain-union bound
-- statement:
--   Let $n\ge1$ and let $x,y$ be distinct names in $T^{(n)}$. Then
--   $$\bigl(\exists T:\ T\text{ is ordered},\ |T|\le n,\ x,y\in T\bigr)\quad\Longleftrightarrow\quad |C(x)\cup C(y)|\le n.$$
--   This characterizes the conflict relation used in the minimum-flag problem. Both directions and all positive sizes are retained.
--
--   Differences from the source:
--   - encoding: positive integer node words, finite chains and the n-full tree → published List Nat names with positivity, Finset chains and explicit fullTree n; reason: the existing published representation preserves each source name, chain and coexistence edge
-- source:
--   Cong Tian, Runzhe Ma, Wensheng Wang, Zhenhua Duan, Büchi Determinization with Optimal States and Square Root Index Improvement, STOC 2027 submission #1731 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1731.pdf, Lemma 14, p. 11

import Definitions.Def_BuchiRabinIndex_LowerBound_Supplement_Flags

set_option autoImplicit false

namespace BuchiRabinIndex.LowerBound.Supplement

/-- STOC 2027 submission #1731, lemma 14. Statement only. -/
theorem lemma_14 (n : ℕ) (hn : 1 ≤ n) (x y : Node)
    (hx : x ∈ fullTree n) (hy : y ∈ fullTree n) (hne : x ≠ y) :
    (∃ T : Finset Node, Ordered T ∧ T.card ≤ n ∧ x ∈ T ∧ y ∈ T) ↔
      (chain x ∪ chain y).card ≤ n := by sorry

end BuchiRabinIndex.LowerBound.Supplement
