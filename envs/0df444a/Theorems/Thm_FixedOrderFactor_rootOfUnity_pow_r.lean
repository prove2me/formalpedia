-- Prove2me | Theorems.Thm_FixedOrderFactor_rootOfUnity_pow_r
-- name    : FixedOrderFactor.rootOfUnity_pow_r
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:49:04.602717+00:00
-- url     : https://prove2.me/theorems/b3465cf7-e91e-5297-9e55-4f3b6647198c
-- title:
--   Fixed Order Factor: root Of Unity pow r
-- statement:
--   The Fixed Order Factor construction uses the root Of Unity pow r property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/Local.lean#L13-L15
-- source:
--   https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/Local.lean#L13-L15

module
public import Definitions.Def_FixedOrderFactor_Defs
public import Definitions.Def_FixedOrderFactor_Local
set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology Complex Finset
open FixedOrderFactor

theorem FixedOrderFactor.rootOfUnity_pow_r {r : ℕ} (hr : 0 < r) (j : ℕ) : rootOfUnity r j ^ r = 1 := by sorry
