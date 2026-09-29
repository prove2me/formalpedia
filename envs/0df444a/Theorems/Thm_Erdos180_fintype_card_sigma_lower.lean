-- Prove2me | Theorems.Thm_Erdos180_fintype_card_sigma_lower
-- name    : Erdos180.fintype_card_sigma_lower
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-04T02:10:21.85261+00:00
-- url     : https://prove2.me/theorems/be001669-a673-4897-b87a-1ea8e96f383c
-- title:
--   Lower bound for a dependent sum
-- statement:
--   If a base type has at least $b$ elements and every fibre has at least $f$ elements, the
--   total space of the dependent sum has at least $b \cdot f$ elements.
--
--   The elementary counting principle that turns the per-step bound of the previous lemma into the
--   global walk count $d(d-1)^3$ of Lemma 3.2.
-- source:
--   https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/CompactnessAndDegeneracy.lean#L3199-L3213

import Definitions.Def_erdos180_core4
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators

open Erdos180
open SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem Erdos180.fintype_card_sigma_lower
    {α : Type*} [Fintype α]
    {β : α → Type*} [∀ a, Fintype (β a)]
    {baseLower fiberLower : ℕ}
    (hbase : baseLower ≤ Fintype.card α)
    (hfiber : ∀ a : α, fiberLower ≤ Fintype.card (β a)) :
    baseLower * fiberLower ≤ Fintype.card (Sigma β) := by sorry
