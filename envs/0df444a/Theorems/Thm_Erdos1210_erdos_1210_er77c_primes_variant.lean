-- Prove2me | Theorems.Thm_Erdos1210_erdos_1210_er77c_primes_variant
-- name    : Erdos1210.erdos_1210_er77c_primes_variant
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-25T17:10:42.71292+00:00
-- url     : https://prove2.me/theorems/558fc898-4759-4b89-9b06-3c21585ab2a4
-- title:
--   Erdős 1210, [Er77c] variant: primes in $(n,m]$
-- statement:
--   **The [Er77c] form of the problem (affirmative form).** There is an absolute constant $C$ such that for all integers $0\le n<m$, if $q_1<\dots<q_k$ are the primes in $(n,m]$, then
--   $$
--   \sum_{i=1}^{k}\frac{1}{q_i-n}\;<\;\sum_{p<m-n}\frac1p+C .
--   $$
--   In [Er80] Erdős wrote that he had not stated the problem quite correctly in [Er77c]; this is the version from [Er77c] that erdosproblems.com identifies as presumably meant. It is the special case of the pairwise-coprime question in which the set consists of primes in an interval, measured from its left endpoint.
--
--   **Formalization Note** Affirmative form of the Formal Conjectures variant `erdos_1210.variants.er80_correction`; a disproof establishes the negative answer.
-- source:
--   Erdős Problem #1210, https://www.erdosproblems.com/1210 (remark on [Er77c, p.64] and [Er80, p.112]); Lean encoding follows Formal Conjectures ErdosProblems/1210.lean, theorem erdos_1210.variants.er80_correction (affirmative direction).

import Mathlib
open Finset

namespace Erdos1210

theorem erdos_1210_er77c_primes_variant :
    ∃ C : ℝ, ∀ n m : ℕ, n < m →
      ∑ q ∈ (Ioc n m).filter Nat.Prime, (1 / ((q : ℝ) - n)) <
        (∑ p ∈ (range (m - n)).filter Nat.Prime, (1 / (p : ℝ))) + C := by sorry

end Erdos1210
