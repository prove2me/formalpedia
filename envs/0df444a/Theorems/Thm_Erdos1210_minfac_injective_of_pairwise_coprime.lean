-- Prove2me | Theorems.Thm_Erdos1210_minfac_injective_of_pairwise_coprime
-- name    : Erdos1210.minfac_injective_of_pairwise_coprime
-- status  : Proved
-- author  : @junyihjy
-- created : 2026-09-30T16:34:33.833474+00:00
-- url     : https://prove2.me/theorems/6b7867d1-ddd1-4a6d-950b-21d8d571ed1e
-- title:
--   Least-prime-factor map is injective on pairwise coprime sets (Erdos 1210 lemma)
-- statement:
--   Let A be a finite set of natural numbers that is pairwise coprime (gcd(a,b) = 1 for distinct a, b ∈ A). Then the least-prime-factor map a ↦ minFac a is injective on {a ∈ A : a ≥ 2}: two distinct elements ≥ 2 cannot share a least prime factor p, since p would then divide both and hence divide their gcd, contradicting coprimality. Elementary lemma for Erdős Problem 1210.
-- source:
--   Erdős Problem #1210, https://www.erdosproblems.com/1210 — elementary lemma isolating the usable half of the least-prime-factor reduction.

import Mathlib

namespace Erdos1210

theorem minfac_injective_of_pairwise_coprime :
    ∀ A : Finset ℕ,
      (∀ a ∈ A, ∀ b ∈ A, a ≠ b → a.Coprime b) →
      Set.InjOn (fun a => a.minFac) {a ∈ (↑A : Set ℕ) | 2 ≤ a} := by sorry

end Erdos1210
