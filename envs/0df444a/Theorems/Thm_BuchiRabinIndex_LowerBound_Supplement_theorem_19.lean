-- Prove2me | Theorems.Thm_BuchiRabinIndex_LowerBound_Supplement_theorem_19
-- name    : BuchiRabinIndex.LowerBound.Supplement.theorem_19
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T13:52:31.933083+00:00
-- url     : https://prove2.me/theorems/7032d8ba-29be-4fd6-a2db-71a3ad366d87
-- title:
--   Theorem 19 — Canonical flag correctness: distinctness and exact range
-- statement:
--   Let $n\ge1$, and let cf be the literal recursive function of Definition 17. It satisfies both conclusions:
--
--   1. If $x\ne y$ are in $T^{(n)}$, have equal weight and $|C(x)\cup C(y)|\le n$, then $\operatorname{cf}(n,x)\ne\operatorname{cf}(n,y)$.
--   2. At every weight $w$,
--   $$\{\operatorname{cf}(n,x):x\in T^{(n)},\ \operatorname{weight}(x)=w\}=\{1,\ldots,\operatorname{sf}(n,w)\}.$$
--   The second conclusion asserts every flag in the stated interval is attained. For $w\ge n$ no name has weight $w$ and $\operatorname{sf}(n,w)=0$, so both sides are empty; the proof on p. 16 treats $0\le w\le n-1$. These properties establish the canonical identifiers used by the reduced condition.
--
--   Differences from the source:
--   - encoding: positive integer node words, finite chains and the n-full tree → published List Nat names with positivity, Finset chains and explicit fullTree n; reason: the existing published representation preserves each source name, chain and coexistence edge
--   - encoding: the threshold is ceil((n-1)/2) for positive n → natural division n / 2; reason: these integers agree for every n ≥ 1; all subtractions and exponents are exact on the stated branches
--   - encoding: the finite chromatic numbers of G_n and its weight subgraphs → Mathlib chromaticNumber converted to Nat; reason: these graphs have finite carriers, so their chromatic numbers are finite; no infinite default is used
-- source:
--   Cong Tian, Runzhe Ma, Wensheng Wang, Zhenhua Duan, Büchi Determinization with Optimal States and Square Root Index Improvement, STOC 2027 submission #1731 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1731.pdf, Theorem 19, p. 15

import Definitions.Def_BuchiRabinIndex_LowerBound_Supplement_Flags

set_option autoImplicit false

namespace BuchiRabinIndex.LowerBound.Supplement

/-- STOC 2027 submission #1731, theorem 19. Statement only. -/
theorem theorem_19 (n : ℕ) (hn : 1 ≤ n) :
    (∀ x ∈ fullTree n, ∀ y ∈ fullTree n, x ≠ y → weight x = weight y →
      (chain x ∪ chain y).card ≤ n → cf n x ≠ cf n y) ∧
    (∀ w : ℕ,
      ((fullTree n).filter fun x => weight x = w).image (cf n) =
        Finset.Icc 1 (sf n w)) := by sorry

end BuchiRabinIndex.LowerBound.Supplement
