-- Prove2me | Theorems.Thm_FixedOrderFactor_zPow_mul_conj
-- name    : FixedOrderFactor.zPow_mul_conj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:55:49.674099+00:00
-- url     : https://prove2.me/theorems/b92fca32-0742-4f43-9ae7-4d8ea82c7ca6
-- title:
--   Fixed Order Factor: z Pow mul conj
-- statement:
--   The Fixed Order Factor construction uses the z Pow mul conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/ModelPairs.lean#L107-L117
-- source:
--   https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/ModelPairs.lean#L107-L117

module
public import Definitions.Def_FixedOrderFactor_Defs
public import Definitions.Def_FixedOrderFactor_Pairs
public import Definitions.Def_FixedOrderFactor_ModelPairs
set_option autoImplicit true
@[expose] public section
public section
open Finset Complex
open FixedOrderFactor

theorem FixedOrderFactor.zPow_mul_conj (r : ℕ) (S : Finset Nat.Primes) (j : S → Fin r) (m n : ℕ) :
    zPow r S j m * starRingEnd ℂ (zPow r S j n) =
      ∏ q : S, ω r ^ (((j q : ℕ) : ℤ) *
        ((m.factorization (q : Nat.Primes) : ℤ) - n.factorization (q : Nat.Primes))) := by sorry
