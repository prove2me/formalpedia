-- Prove2me | Theorems.Thm_FixedOrderFactor_one_sub_mul_ne_zero
-- name    : FixedOrderFactor.one_sub_mul_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:49:10.447865+00:00
-- url     : https://prove2.me/theorems/e1cecc44-d2f7-4613-8965-36de5ef74519
-- title:
--   Fixed Order Factor: one sub mul ne zero
-- statement:
--   The Fixed Order Factor construction uses the one sub mul ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/Local.lean#L28-L34
-- source:
--   https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/Local.lean#L28-L34

module
public import Definitions.Def_FixedOrderFactor_Defs
public import Definitions.Def_FixedOrderFactor_Local
set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology Complex Finset
open FixedOrderFactor

theorem FixedOrderFactor.one_sub_mul_ne_zero {r : ℕ} (hr : 0 < r) (j : ℕ) {x : ℂ} (hx : x ^ r ≠ 1) :
    1 - rootOfUnity r j * x ≠ 0 := by sorry
