-- Prove2me | Theorems.Thm_EqualSubsetSum_Faster_lemma_4_5
-- name    : EqualSubsetSum.Faster.lemma_4_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T23:27:05.994495+00:00
-- url     : https://prove2.me/theorems/a6cbd61e-f6fa-495e-ac0b-03d04b69a3db
-- title:
--   Lemma 4.5 — weighted parity bound ∑_{v ∈ D_T} 2^{−c(v)} ≤ 2
-- statement:
--   Let $z\in\mathbb Z^n$ and suppose that every solution for $z$ has more than $2n/3$ nonzero entries. Fix $T\subseteq\{1,\dots,n\}$ and let $D_T$ be the set of vectors $v\in\{-2,\dots,2\}^n$ with $v\cdot z=0$ whose odd entries are exactly those in $T$. With $c(v)$ the number of entries $\pm2$ of $v$,
--   $$\sum_{v\in D_T}2^{-c(v)}\le 2 .$$
--   It is the only step of the report bound of the arithmetic procedure that uses minimum support.
--
--   Differences from the source:
--   - encoding: T ⊆ {1, …, n} → T : Finset (Fin n) (indices 0, …, n − 1); reason: 0-based indexing; same sets
-- source:
--   Cheshm Jahan, Keshavarz Hedayati, Safari, Shahrezaei, Faster Equal-Subset-Sum via Truncated Inclusion–Exclusion, STOC 2027 submission (manuscript, sha256 7ad8c8b2…61dacd1), p. 28, Lemma 4.5

import Mathlib
import Definitions.Def_EqualSubsetSum_Faster_Problem
import Definitions.Def_EqualSubsetSum_Faster_Cube

namespace EqualSubsetSum.Faster

/-- Lemma 4.5 (p. 28). If every solution for `z` has more than `2n/3` nonzero entries, then for
every `T ⊆ {1, …, n}`, `∑_{v ∈ D_T} 2^{-c(v)} ≤ 2`, where `D_T` is the set of `v ∈ {-2, …, 2}ⁿ`
with `v · z = 0` whose odd entries are exactly those in `T`, and `c(v)` counts the entries `±2`. -/
theorem lemma_4_5 {n : ℕ} (z : Fin n → ℤ)
    (hz : ∀ d, IsSolution z d → (2 * n : ℝ) / 3 < (supp d).card) (T : Finset (Fin n)) :
    ∑ v ∈ parityClass z T, ((2 : ℝ) ^ doubledCount v)⁻¹ ≤ 2 := by sorry

end EqualSubsetSum.Faster
