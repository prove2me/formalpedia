-- Prove2me | Theorems.Thm_BuchiRabinIndex_LowerBound_Supplement_lemma_15
-- name    : BuchiRabinIndex.LowerBound.Supplement.lemma_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T13:52:02.734342+00:00
-- url     : https://prove2.me/theorems/072d2dca-61a8-4fed-b330-64880d9f9f0c
-- title:
--   Lemma 15 — Exact minimum flag counts at every weight
-- statement:
--   For $n\ge1$, sf is the independently defined chromatic minimum at a fixed weight. Its values are
--   $$\operatorname{sf}(n,0)=1,$$
--   $$\operatorname{sf}(n,w)=2^{w-1}\quad(0<w\le\lceil(n-1)/2\rceil),$$
--   $$\operatorname{sf}(n,w)=2^{n-w-1}\quad(\lceil(n-1)/2\rceil<w<n).$$
--   These are optimal flag counts, not just bounds for one chosen colouring. The root case and both positive-weight regimes are included.
--
--   Differences from the source:
--   - encoding: positive integer node words, finite chains and the n-full tree → published List Nat names with positivity, Finset chains and explicit fullTree n; reason: the existing published representation preserves each source name, chain and coexistence edge
--   - encoding: the threshold is ceil((n-1)/2) for positive n → natural division n / 2; reason: these integers agree for every n ≥ 1; all subtractions and exponents are exact on the stated branches
--   - encoding: the finite chromatic numbers of G_n and its weight subgraphs → Mathlib chromaticNumber converted to Nat; reason: these graphs have finite carriers, so their chromatic numbers are finite; no infinite default is used
-- source:
--   Cong Tian, Runzhe Ma, Wensheng Wang, Zhenhua Duan, Büchi Determinization with Optimal States and Square Root Index Improvement, STOC 2027 submission #1731 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1731.pdf, Lemma 15, p. 12

import Definitions.Def_BuchiRabinIndex_LowerBound_Supplement_Flags

set_option autoImplicit false

namespace BuchiRabinIndex.LowerBound.Supplement

/-- STOC 2027 submission #1731, lemma 15. Statement only. -/
theorem lemma_15 (n : ℕ) (hn : 1 ≤ n) :
    sf n 0 = 1 ∧
    (∀ w : ℕ, 0 < w → w ≤ n / 2 → sf n w = 2 ^ (w - 1)) ∧
    (∀ w : ℕ, n / 2 < w → w < n → sf n w = 2 ^ (n - w - 1)) := by sorry

end BuchiRabinIndex.LowerBound.Supplement
