-- Prove2me | Theorems.Thm_FixedOrderFactor_mem_primesUpTo
-- name    : FixedOrderFactor.mem_primesUpTo
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:51:21.582928+00:00
-- url     : https://prove2.me/theorems/18a62b05-e959-5b69-879f-4e97a255f0f5
-- title:
--   Fixed Order Factor: mem primes Up To
-- statement:
--   The Fixed Order Factor construction uses the mem primes Up To property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/Model.lean#L59-L68
-- source:
--   https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/Model.lean#L59-L68

module
public import Definitions.Def_FixedOrderFactor_Euler
public import Definitions.Def_FixedOrderFactor_Local
public import Definitions.Def_FixedOrderFactor_Model
set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology Finset
open FixedOrderFactor

theorem FixedOrderFactor.mem_primesUpTo (N : Finset Nat.Primes) (Y : ℕ) (q : Nat.Primes) :
    q ∈ primesUpTo N Y ↔ (q : ℕ) ≤ Y ∧ q ∉ N := by sorry
