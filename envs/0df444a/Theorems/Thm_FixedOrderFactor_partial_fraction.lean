-- Prove2me | Theorems.Thm_FixedOrderFactor_partial_fraction
-- name    : FixedOrderFactor.partial_fraction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:51:03.455394+00:00
-- url     : https://prove2.me/theorems/ae115479-68aa-5e27-99ae-159086c6ae44
-- title:
--   Fixed Order Factor: partial fraction
-- statement:
--   The Fixed Order Factor construction uses the partial fraction property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/Local.lean#L69-L74
-- source:
--   https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/Local.lean#L69-L74

module
public import Definitions.Def_FixedOrderFactor_Defs
public import Definitions.Def_FixedOrderFactor_Local
set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology Complex Finset
open FixedOrderFactor

theorem FixedOrderFactor.partial_fraction {a b t : ℂ} (ha : 1 - a ≠ 0) (hb : 1 - b ≠ 0) (hab : a * b = t)
    (ht : 1 - t ≠ 0) :
    1 / ((1 - a) * (1 - b)) = (1 / (1 - t)) * (1 / (1 - a) + 1 / (1 - b) - 1) := by sorry
