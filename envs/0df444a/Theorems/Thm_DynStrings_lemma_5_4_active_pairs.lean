-- Prove2me | Theorems.Thm_DynStrings_lemma_5_4_active_pairs
-- name    : DynStrings.lemma_5_4_active_pairs
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:55:53.80824+00:00
-- url     : https://prove2.me/theorems/37181ee8-7d8a-4f4d-9fdc-988568de0ab4
-- title:
--   Lemma 5.4 — the number of active pairs $(A,k)$ is $O(\Lambda(X\mid\mathcal C))$
-- statement:
--   There is an absolute constant $C_0$ such that for every non-empty string $X$, every finite collection $\mathcal C$ and every choice of the orders, the set of pairs $(A,k)$ with $k\ge0$ such that
--
--   1. $X_k$ is non-singleton and $A$ is a symbol of $X_k$ active in round $k+1$, and
--   2. $A$ occurs in no non-singleton level-$k$ word $Y_k$ with $Y\in\mathcal C$,
--
--   is finite and has at most $C_0\,\Lambda(X\mid\mathcal C)$ elements.
--
--   This deterministic count bounds the exclusive symbols of $X$ and the number of order comparisons that a new string requires on top of a stored collection.
--
--   Differences from the source:
--   - generalization: strings over a fixed countably infinite alphabet $\Sigma$ → strings over an arbitrary type $\alpha$ with decidable equality; reason: the statement holds for every alphabet type, and a countably infinite $\alpha$ gives the source's statement
--   - encoding: O(·) with absolute constants → an explicit constant quantified before the alphabet, the strings and the orders; reason: the paper's convention (p.13) that hidden constants are absolute
--   - encoding: every choice of the orders → every family `lt` with `IsOrderFamily lt` (strict total orders on all syntactic symbols for even k ≥ 2, paused before active); reason: the parse reads only well-formed symbols, so orders on the larger syntactic type restrict to exactly the source's orders
--   - encoding: the number of pairs (A, k), k ≥ 0 → the set of pairs over all k ∈ ℕ is finite and its `ncard` is bounded; reason: a bare cardinality of a possibly infinite set would be 0 in Lean
-- source:
--   Duyster, Kociumaka, Komlós, Optimal Dynamic Strings in Compressed Space (manuscript, sha256 cfcb3de9…), Lemma 5.4, p.22

import Mathlib
import Definitions.Def_DynStrings_Novelty

namespace DynStrings

/-- **Lemma 5.4** (active pairs), p.22.
Duyster, Kociumaka, Komlós, *Optimal Dynamic Strings in Compressed Space* (manuscript, sha256 cfcb3de9…)

For every non-empty string `X`, every finite collection `𝒞`, and every choice of the orders, the
number of pairs `(A, k)` with `k ≥ 0` such that `X_k` is non-singleton, `A` is a symbol of `X_k`
active in round `k + 1`, and `A` occurs in no non-singleton level-`k` word `Y_k` with `Y ∈ 𝒞`, is
`O(Λ(X | 𝒞))`.

**Formalization Note.** The set of pairs ranges over all levels `k ∈ ℕ`; the statement asserts it
is finite and bounds its cardinality. -/
theorem lemma_5_4_active_pairs :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ (α : Type) [DecidableEq α] (X : List α) (𝒞 : Multiset (List α))
      (lt : ℕ → StrSym α → StrSym α → Prop), X ≠ [] → IsOrderFamily lt →
      (activePairs lt X 𝒞).Finite ∧ ((activePairs lt X 𝒞).ncard : ℝ) ≤ C₀ * Lam X 𝒞 := by sorry

end DynStrings
