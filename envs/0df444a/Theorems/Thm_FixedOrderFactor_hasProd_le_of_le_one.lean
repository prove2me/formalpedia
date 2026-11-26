-- Prove2me | Theorems.Thm_FixedOrderFactor_hasProd_le_of_le_one
-- name    : FixedOrderFactor.hasProd_le_of_le_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:51:58.416689+00:00
-- url     : https://prove2.me/theorems/bea2fe40-3ffa-4b30-b0bb-0b6807ed766c
-- title:
--   Fixed Order Factor: has Prod le of le one
-- statement:
--   The Fixed Order Factor construction uses the has Prod le of le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/Order.lean#L19-L27
-- source:
--   https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/Order.lean#L19-L27

module
public import Definitions.Def_FixedOrderFactor_Model
public import Definitions.Def_FixedOrderFactor_Order
set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology Finset
open FixedOrderFactor

theorem FixedOrderFactor.hasProd_le_of_le_one {ι : Type*} [DecidableEq ι] {f : ι → ℝ} {a : ℝ} (h : HasProd f a)
    (hf0 : ∀ i, 0 ≤ f i) (hf : ∀ i, f i ≤ 1) (i₀ : ι) : a ≤ f i₀ := by sorry
