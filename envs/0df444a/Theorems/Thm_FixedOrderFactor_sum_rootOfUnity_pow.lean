-- Prove2me | Theorems.Thm_FixedOrderFactor_sum_rootOfUnity_pow
-- name    : FixedOrderFactor.sum_rootOfUnity_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:51:10.240036+00:00
-- url     : https://prove2.me/theorems/d6b3f5af-7985-4cb8-b886-091148d94eb7
-- title:
--   Fixed Order Factor: sum root Of Unity pow
-- statement:
--   The Fixed Order Factor construction uses the sum root Of Unity pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/Local.lean#L17-L26
-- source:
--   https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/Local.lean#L17-L26

module
public import Definitions.Def_FixedOrderFactor_Defs
public import Definitions.Def_FixedOrderFactor_Local
set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology Complex Finset
open FixedOrderFactor

theorem FixedOrderFactor.sum_rootOfUnity_pow {r : ℕ} (hr : 0 < r) (m : ℕ) (hm : m < r) :
    ∑ j ∈ range r, rootOfUnity r j ^ m = if m = 0 then (r : ℂ) else 0 := by sorry
