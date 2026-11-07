-- Prove2me | Theorems.Thm_DynStrings_claim_5_9_level_sums
-- name    : DynStrings.claim_5_9_level_sums
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:55:35.767653+00:00
-- url     : https://prove2.me/theorems/5fd19109-deb3-433e-9cb2-3dc223566233
-- title:
--   Claim 5.9 — $\sum_{k\in K}\Delta_{k,m}=O(\Lambda)$ and $\max_{k\in K}\Delta_{k,m}\le\gamma$ for dyadic $m\ge2$
-- statement:
--   There is an absolute constant $C_0$ such that for every non-empty string $X$, every finite collection $\mathcal C$ and every dyadic $m\ge2$,
--
--   $$\sum_{k\in K}\Delta_{k,m}\le C_0\,\Lambda\qquad\text{and}\qquad \max_{k\in K}\Delta_{k,m}\le\gamma,$$
--
--   where $K=\{k:1\le k<\kappa(|X|),\ k\text{ odd}\}$, $\Lambda=\Lambda(X\mid\mathcal C)$ and $\gamma=1+\delta(X\mid\mathcal C)$.
--
--   The local novelties of the levels add up to the dyadic novelty, uniformly in the arity scale $m$; this is how the per-level bounds combine into the moment-generating function bound.
--
--   Differences from the source:
--   - generalization: strings over a fixed countably infinite alphabet $\Sigma$ → strings over an arbitrary type $\alpha$ with decidable equality; reason: the statement holds for every alphabet type, and a countably infinite $\alpha$ gives the source's statement
--   - reading: X and C fixed in §5 (Theorem 5.1 assumes X non-empty) → the hypothesis `X ≠ []`; reason: standing assumption of §5, under which the statement is proved
--   - encoding: O(·) with absolute constants → an explicit constant quantified before the alphabet, the strings and the orders; reason: the paper's convention (p.13) that hidden constants are absolute
--   - encoding: dyadic m ≥ 2; max over k ∈ K → m = 2^p with 2 ≤ m; the bound for every k ∈ K; reason: a dyadic integer is a power of two (p.13); a maximum is bounded iff every term is
-- source:
--   Duyster, Kociumaka, Komlós, Optimal Dynamic Strings in Compressed Space (manuscript, sha256 cfcb3de9…), Claim 5.9, p.24

import Mathlib
import Definitions.Def_DynStrings_Novelty

namespace DynStrings

/-- **Claim 5.9** (level sums), p.24.
Duyster, Kociumaka, Komlós, *Optimal Dynamic Strings in Compressed Space* (manuscript, sha256 cfcb3de9…)

There is an absolute constant `C₀` such that, for every non-empty string `X`, finite collection
`𝒞` and dyadic `m ≥ 2`, `∑_{k ∈ K} Δ_{k,m} ≤ C₀ Λ` and `max_{k ∈ K} Δ_{k,m} ≤ γ`, where
`Λ = Λ(X | 𝒞)`, `γ = 1 + δ(X | 𝒞)` and `K = {k : 1 ≤ k < κ(|X|), k odd}`.

**Formalization Note.** `m` dyadic is `m = 2^p`; the maximum is stated for every `k ∈ K`. -/
theorem claim_5_9_level_sums :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ (α : Type) [DecidableEq α] (X : List α) (𝒞 : Multiset (List α)),
      X ≠ [] → ∀ m p : ℕ, m = 2 ^ p → 2 ≤ m →
      (∑ k ∈ Kset X.length, DeltaLoc X 𝒞 k m ≤ C₀ * Lam X 𝒞) ∧
      ∀ k ∈ Kset X.length, DeltaLoc X 𝒞 k m ≤ 1 + deltaRel X 𝒞 := by sorry

end DynStrings
