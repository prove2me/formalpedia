-- Prove2me | Theorems.Thm_DynStrings_lemma_5_3_witness_fragments
-- name    : DynStrings.lemma_5_3_witness_fragments
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:55:39.091224+00:00
-- url     : https://prove2.me/theorems/29c94c09-1ff4-48eb-b49e-597408b4eab5
-- title:
--   Lemma 5.3 — all word and tuple witnesses lie in $O(\Delta_{k,m})$ fragments of length $O(m)$ determined by $X_k$
-- statement:
--   There is an absolute constant $C_0$ such that the following holds. Let $X$ be a string and $\mathcal C$ a finite collection, and let $k\ge0$ and $m\ge1$. There is a family $F_{k,m}$ of fragments of the level word $X_k$, determined by $X,\mathcal C,k,m$ and $X_k$ alone, such that for every choice of the orders
--
--   1. $F_{k,m}$ has at most $C_0\,\Delta_{k,m}$ members, each of at most $C_0\,m$ symbols;
--   2. every word witness is contained in a member of $F_{k,m}$;
--   3. for odd $k$, every tuple witness is contained in a member of $F_{k,m}$.
--
--   New symbols at level $k$ can only appear in few, short, predetermined places. Because the family depends on the orders only through $X_k$, it is fixed by the history of the first $k$ rounds, which is what the probabilistic argument conditions on.
--
--   Differences from the source:
--   - generalization: strings over a fixed countably infinite alphabet $\Sigma$ → strings over an arbitrary type $\alpha$ with decidable equality; reason: the statement holds for every alphabet type, and a countably infinite $\alpha$ gives the source's statement
--   - encoding: O(·) with absolute constants → an explicit constant quantified before the alphabet, the strings and the orders; reason: the paper's convention (p.13) that hidden constants are absolute
--   - encoding: every choice of the orders → every family `lt` with `IsOrderFamily lt` (strict total orders on all syntactic symbols for even k ≥ 2, paused before active); reason: the parse reads only well-formed symbols, so orders on the larger syntactic type restrict to exactly the source's orders
--   - encoding: the family is determined by X, C, k, m, and X_k → a map Φ from level words to finite sets of index intervals, chosen from X, C, k, m before the orders, applied to X_k; reason: this is the meaning of 'determined by'; the family's members are fragments of X_k
-- source:
--   Duyster, Kociumaka, Komlós, Optimal Dynamic Strings in Compressed Space (manuscript, sha256 cfcb3de9…), Lemma 5.3, p.21

import Mathlib
import Definitions.Def_DynStrings_Novelty

namespace DynStrings

/-- **Lemma 5.3** (witness fragments), p.21.
Duyster, Kociumaka, Komlós, *Optimal Dynamic Strings in Compressed Space* (manuscript, sha256 cfcb3de9…)

There is an absolute constant `C₀` such that, for every string `X`, finite collection `𝒞`, `k ≥ 0` and `m ≥ 1`, there is a family `F_{k,m}` of at most `C₀ Δ_{k,m}` fragments of `X_k`,
each of length at most `C₀ m`, such that every word witness and, for odd `k`, every tuple witness
is contained in a member of `F_{k,m}`. The family is determined by `X, 𝒞, k, m` and `X_k`.

**Formalization Note.** "Determined by `X, 𝒞, k, m`, and `X_k`" is a map `Φ` chosen from
`X, 𝒞, k, m` before the orders, applied to `X_k`. Fragments are index intervals `[p₁, p₂)` of
`X_k`. `O(·)` is an absolute constant placed before every quantifier. -/
theorem lemma_5_3_witness_fragments :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ (α : Type) [DecidableEq α] (X : List α) (𝒞 : Multiset (List α))
      (k m : ℕ), 1 ≤ m →
      ∃ Φ : List (StrSym α) → Finset (ℕ × ℕ), ∀ lt : ℕ → StrSym α → StrSym α → Prop,
        IsOrderFamily lt →
        ((Φ (level lt X k)).card : ℝ) ≤ C₀ * DeltaLoc X 𝒞 k m ∧
        (∀ p ∈ Φ (level lt X k), p.1 ≤ p.2 ∧ p.2 ≤ (level lt X k).length ∧
          ((p.2 - p.1 : ℕ) : ℝ) ≤ C₀ * m) ∧
        (∀ i j, IsWordWitness lt X 𝒞 k m i j → ∃ p ∈ Φ (level lt X k), p.1 ≤ i ∧ j ≤ p.2) ∧
        (Odd k → ∀ a b, IsTupleWitness lt X 𝒞 k m a b →
          ∃ p ∈ Φ (level lt X k), p.1 ≤ a ∧ b ≤ p.2) := by sorry

end DynStrings
