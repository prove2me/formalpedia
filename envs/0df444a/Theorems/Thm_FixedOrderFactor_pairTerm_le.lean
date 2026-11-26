-- Prove2me | Theorems.Thm_FixedOrderFactor_pairTerm_le
-- name    : FixedOrderFactor.pairTerm_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:53:58.726828+00:00
-- url     : https://prove2.me/theorems/56fc3732-8983-4d1d-bc09-3fddc94b7440
-- title:
--   Fixed Order Factor: pair Term le
-- statement:
--   The Fixed Order Factor construction uses the pair Term le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/Diagonal.lean#L38-L44
-- source:
--   https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/Diagonal.lean#L38-L44

module
public import Definitions.Def_FixedOrderFactor_Values
public import Definitions.Def_FixedOrderFactor_Diagonal
set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology Finset
open FixedOrderFactor

theorem FixedOrderFactor.pairTerm_le (N : Finset Nat.Primes) (r : ℕ) (ab : ℕ × ℕ) :
    pairTerm N r ab ≤ zterm N r ab.1 * zterm N r ab.2 := by sorry
