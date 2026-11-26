-- Prove2me | Theorems.Thm_FixedOrderFactor_exists_prime_not_mem
-- name    : FixedOrderFactor.exists_prime_not_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:49:32.501439+00:00
-- url     : https://prove2.me/theorems/0363b87b-bd9c-58d9-9e98-30cb5ab47bc7
-- title:
--   Fixed Order Factor: exists prime not mem
-- statement:
--   The Fixed Order Factor construction uses the exists prime not mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/Order.lean#L29-L33
-- source:
--   https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/Order.lean#L29-L33

module
public import Definitions.Def_FixedOrderFactor_Model
public import Definitions.Def_FixedOrderFactor_Order
set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology Finset
open FixedOrderFactor

theorem FixedOrderFactor.exists_prime_not_mem (N : Finset Nat.Primes) : ∃ q : Nat.Primes, q ∉ N := by sorry
