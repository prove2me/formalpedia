-- Prove2me | Theorems.Thm_ExactPatternStream_lemma_6_2
-- name    : ExactPatternStream.lemma_6_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:03:31.186514+00:00
-- url     : https://prove2.me/theorems/8cc10d4a-68e8-4693-b385-58c0e09385cd
-- title:
--   Lemma 6.2 — the lines $D_v$ lie in $O((n/m)\log(2m))$ planes
-- statement:
--   Let $F$ be a field and $P\in(F^3)^m$, $T\in(F^3)^n$, $1\le m\le n$. For $0\le v\le n-m$, let $D_v=\mathrm{span}\{T[v+t]-P[t]:0\le t<m\}$. All $D_v$ that are lines are contained in $O\big(\frac nm\log(2m)\big)$ two-dimensional subspaces of $F^3$.
--
--   This replaces a union bound over positions by a union bound over planes.
--
--   Differences from the source:
--   - encoding: $O(\cdot)$ → one absolute $K$ before all variables, with $\log_2$; reason: the same bounds up to a constant
-- source:
--   Gawrychowski, Janczewski, Jin, Nelson, An Improved Streaming Algorithm for Exact Pattern Matching (preprint, STOC 2027 submission, sha256 351218cb…), Lemma 6.2, p.16 (PDF 17)

import Mathlib
import Definitions.Def_ExactPatternStream_LinearMaps

namespace ExactPatternStream

/-- Gawrychowski, Janczewski, Jin, Nelson, *An Improved Streaming Algorithm for Exact Pattern Matching* (preprint, STOC 2027 submission, sha256 351218cb…), Lemma 6.2, p.16 (PDF 17).

For `P ∈ (F³)^m`, `T ∈ (F³)^n`, `1 ≤ m ≤ n`, all `D_v`, `0 ≤ v ≤ n - m`, that are lines lie in `O((n/m) log(2m))` two-dimensional subspaces of `F³`.

**Formalization Note.** `F` is any field, as in §6, p.15. "Contained in" means each such line lies in one of the planes. `O(·)` is an absolute `K` before the field, and the quotient `n/m` is real. -/
theorem lemma_6_2 : ∃ K : ℝ, ∀ (F : Type*) [Field F] (m n : ℕ) (P : Fin m → Fin 3 → F)
    (T : Fin n → Fin 3 → F), 1 ≤ m → m ≤ n →
    ∃ U : Finset (Submodule F (Fin 3 → F)),
      (∀ W ∈ U, Module.finrank F W = 2) ∧
      (U.card : ℝ) ≤ K * ((n : ℝ) / m) * Real.logb 2 (2 * m) ∧
      ∀ v : ℕ, v ≤ n - m → Module.finrank F (mismatchSpan F P T v) = 1 →
        ∃ W ∈ U, mismatchSpan F P T v ≤ W := by sorry

end ExactPatternStream
