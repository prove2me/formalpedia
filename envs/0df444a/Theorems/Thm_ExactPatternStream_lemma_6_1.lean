-- Prove2me | Theorems.Thm_ExactPatternStream_lemma_6_1
-- name    : ExactPatternStream.lemma_6_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:03:25.730883+00:00
-- url     : https://prove2.me/theorems/4b9a86f0-3045-43d3-b0e4-7ce7c34ba2f7
-- title:
--   Lemma 6.1 — $O(\log|T|)$ lines of the form $\Delta_p(T)$ in $F^2$
-- statement:
--   Let $F$ be a field and $T\in(F^2)^{|T|}$ a nonempty vector string. Then there are $O(\log|T|)$ distinct lines of the form
--   $$\Delta_p(T)=\mathrm{span}\{T[i+p]-T[i]:0\le i<|T|-p\},\qquad1\le p\le|T|/3.$$
--   This is the structural heart of the covering argument: difference spaces of a string form very few lines.
--
--   Differences from the source:
--   - encoding: $O(\cdot)$ → one absolute $K$ before all variables, with $\log_2$; reason: the same bounds up to a constant
-- source:
--   Gawrychowski, Janczewski, Jin, Nelson, An Improved Streaming Algorithm for Exact Pattern Matching (preprint, STOC 2027 submission, sha256 351218cb…), Lemma 6.1, p.15 (PDF 16)

import Mathlib
import Definitions.Def_ExactPatternStream_LinearMaps

namespace ExactPatternStream

/-- Gawrychowski, Janczewski, Jin, Nelson, *An Improved Streaming Algorithm for Exact Pattern Matching* (preprint, STOC 2027 submission, sha256 351218cb…), Lemma 6.1, p.15 (PDF 16).

For a nonempty vector string `T ∈ (F²)^{|T|}` over any field, at most `O(log |T|)` distinct lines have the form `Δ_p(T)` with `1 ≤ p ≤ |T|/3`.

**Formalization Note.** A line is a subspace of `finrank` one. The set of lines is finite, since `p` has finitely many values, so `Set.ncard` is its size. `O(·)` is an absolute `K` before the field; `log₂`. At `|T| ≤ 2` no `p` exists. -/
theorem lemma_6_1 : ∃ K : ℝ, ∀ (F : Type*) [Field F] (n : ℕ) (T : Fin n → Fin 2 → F), 0 < n →
    (({S : Submodule F (Fin 2 → F) | Module.finrank F S = 1 ∧
        ∃ p : ℕ, 1 ≤ p ∧ 3 * p ≤ n ∧ deltaSpan F T p = S}.ncard : ℕ) : ℝ) ≤
      K * Real.logb 2 n := by sorry

end ExactPatternStream
