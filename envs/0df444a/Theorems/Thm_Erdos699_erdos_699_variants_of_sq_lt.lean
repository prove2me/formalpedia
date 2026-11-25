-- Prove2me | Theorems.Thm_Erdos699_erdos_699_variants_of_sq_lt
-- name    : Erdos699.erdos_699.variants.of_sq_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T18:16:06.01169+00:00
-- url     : https://prove2.me/theorems/8d908e9f-0f8e-522a-acdf-49e04c7896c4
-- title:
--   variants: of sq lt
-- statement:
--   Erdős Problem 699 holds when $j^2 < n$: for $1 \le i < j \le n / 2$ with $j^2 < n$ there is a
--   prime $p \ge i$ with $p \mid \gcd\big(\binom{n}{i}, \binom{n}{j}\big)$.
--
--   Source: https://github.com/Paulee314/erdos699-lean/blob/814f545f5f6475786aa5a04e4e795a25cda3670c/Solution.lean#L40-L47
-- source:
--   https://github.com/Paulee314/erdos699-lean/blob/814f545f5f6475786aa5a04e4e795a25cda3670c/Solution.lean#L40-L47

module
public import Definitions.Def_Erdos699_Basic
public import Definitions.Def_Erdos699_Solution
public import Theorems.Thm_Erdos699_of_sq_lt

set_option autoImplicit false
@[expose] public section
public section
open Erdos699

theorem Erdos699.erdos_699.variants.of_sq_lt :
    ∀ n i j : ℕ,
      1 ≤ i →
      i < j →
      j ≤ n / 2 →
      j ^ 2 < n →
      ∃ p : ℕ, p.Prime ∧ i ≤ p ∧ p ∣ Nat.gcd (Nat.choose n i) (Nat.choose n j) := by sorry
