-- Prove2me | Theorems.Thm_FixedOrderFactor_rootOfUnity_eq
-- name    : FixedOrderFactor.rootOfUnity_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:48:00.581129+00:00
-- url     : https://prove2.me/theorems/a8a30dd8-bb4e-5717-aaac-95fd423b314d
-- title:
--   Fixed Order Factor: root Of Unity eq
-- statement:
--   The Fixed Order Factor construction uses the root Of Unity eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/Local.lean#L10-L11
-- source:
--   https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/Local.lean#L10-L11

module
public import Definitions.Def_FixedOrderFactor_Defs
public import Definitions.Def_FixedOrderFactor_Local
set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology Complex Finset
open FixedOrderFactor

theorem FixedOrderFactor.rootOfUnity_eq (r j : ℕ) : rootOfUnity r j = Complex.exp (2 * π * I / r) ^ j := by sorry
