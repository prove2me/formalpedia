-- Prove2me | Theorems.Thm_ChangingCache_UpperBound_Supplement_theorem_A_1
-- name    : ChangingCache.UpperBound.Supplement.theorem_A_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:29:01.607204+00:00
-- url     : https://prove2.me/theorems/66b9249f-9063-43ae-a673-4f3159ed8356
-- title:
--   Theorem A.1 — Factor two after every prefix on non-decreasing profiles
-- statement:
--   Let $m$ be any positive growth-limited memory profile satisfying $m(j)\le m(j+1)$ for every natural $j$, and let $\sigma$ be any finite request sequence. Under $(2,2)$ augmentation, starting with empty caches, after every prefix of length $0\le r\le |\sigma|$,
--   $$F_{\mathrm{LRU}}(\sigma_{<r})\le 2F_{\mathrm{OPT}}(\sigma_{<r}).$$
--   The optimum on the right is computed for that same prefix and profile. Pages may belong to any type with decidable equality. There is no initial-capacity-one, normal-form, greedy-request or bank-invariant hypothesis and no additive term.
--
--   This companion theorem isolates the upper bound for non-decreasing profiles; it is not a step in the proof of the published Theorem 1.1 goal.
--
--   Differences from the source:
--   - encoding: every prefix of a finite request sequence → every natural r ≤ σ.length, with σ.take r for the prefix optimum and the published prefix LRU count; reason: zero-based lists include the empty prefix and leave all finite sequences and all allowed initial capacities arbitrary
-- source:
--   Michael A. Bender, Daniel DeLayo, Pritom Kundu, Charlie McGuffey, Zofia Stefankovic, Zhonglue Wang, STOC 2027 submission #93 (October 2026), p. 23, Theorem A.1; proof pp. 23–24

import Mathlib
import Definitions.Def_ChangingCache_UpperBound_NormalForm

namespace ChangingCache.UpperBound.Supplement

/-- Theorem A.1, pp. 23–24: every prefix, with no normalization or initial-capacity restriction. -/
theorem theorem_A_1 {α : Type*} [DecidableEq α] (m : ℕ → ℕ) (σ : List α)
    (hm : IsMemoryProfile m) (hmono : ∀ j, m j ≤ m (j + 1)) :
    ∀ r ≤ σ.length, lruMissCount (augCap 2 2 m) σ r ≤ 2 * optMisses m (σ.take r) := by sorry

end ChangingCache.UpperBound.Supplement
