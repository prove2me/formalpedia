-- Prove2me | Theorems.Thm_FixedOrderFactor_le_of_hasProd_one_le
-- name    : FixedOrderFactor.le_of_hasProd_one_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:51:27.666742+00:00
-- url     : https://prove2.me/theorems/05f73930-c499-5d7c-a601-05b78fbc22ad
-- title:
--   Fixed Order Factor: le of has Prod one le
-- statement:
--   The Fixed Order Factor construction uses the le of has Prod one le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/Order.lean#L10-L17
-- source:
--   https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/Order.lean#L10-L17

module
public import Definitions.Def_FixedOrderFactor_Model
public import Definitions.Def_FixedOrderFactor_Order
set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology Finset
open FixedOrderFactor

theorem FixedOrderFactor.le_of_hasProd_one_le {ι : Type*} [DecidableEq ι] {f : ι → ℝ} {a : ℝ} (h : HasProd f a)
    (hf : ∀ i, 1 ≤ f i) (i₀ : ι) : f i₀ ≤ a := by sorry
