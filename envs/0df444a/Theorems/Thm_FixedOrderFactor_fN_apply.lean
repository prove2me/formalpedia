-- Prove2me | Theorems.Thm_FixedOrderFactor_fN_apply
-- name    : FixedOrderFactor.fN_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:47:52.951058+00:00
-- url     : https://prove2.me/theorems/6f3fadbc-ce4a-5ca3-a426-6fb8d4e5293d
-- title:
--   Fixed Order Factor: f N apply
-- statement:
--   The Fixed Order Factor construction uses the f N apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/Euler.lean#L31-L36
-- source:
--   https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/Euler.lean#L31-L36

module
public import Definitions.Def_FixedOrderFactor_Defs
public import Definitions.Def_FixedOrderFactor_Euler
set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology
open FixedOrderFactor

theorem FixedOrderFactor.fN_apply (N : Finset Nat.Primes) {s : ℕ} (hs : s ≠ 0) (n : ℕ) :
    fN N s hs n = if 0 < n ∧ PrimeTo N n then 1 / (n : ℝ) ^ s else 0 := by sorry
