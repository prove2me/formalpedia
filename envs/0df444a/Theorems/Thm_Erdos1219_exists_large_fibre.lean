-- Prove2me | Theorems.Thm_Erdos1219_exists_large_fibre
-- name    : Erdos1219.exists_large_fibre
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:43:14.306791+00:00
-- url     : https://prove2.me/theorems/38030cc9-c513-4f06-ac27-8b1e48a0525c
-- title:
--   Erdos1219: exists large fibre
-- statement:
--   Claim A (closure-point argument): if `δ` regresses on the points of big cofinality, then
--   some fibre of `δ` on those points has full cardinality.
--
--   Source: https://github.com/jbaelaw/erdos1219-lean/blob/00e696a9cd2bbd8cad33d2cdc90ad385058c1466/Erdos1219/UnbalancedErdosRado.lean#L144-L204
-- source:
--   https://github.com/jbaelaw/erdos1219-lean/blob/00e696a9cd2bbd8cad33d2cdc90ad385058c1466/Erdos1219/UnbalancedErdosRado.lean#L144-L204

import Definitions.Def_Erdos1219_Defs
import Mathlib.SetTheory.Cardinal.Pigeonhole
import Definitions.Def_Erdos1219_UnbalancedErdosRado
set_option autoImplicit false
open Cardinal Ordinal Set
open Erdos1219
universe u
variable {W : Type u} [LinearOrder W] [WellFoundedLT W]

theorem Erdos1219.exists_large_fibre {μ : Cardinal.{u}} (hμ : ℵ₀ ≤ μ)
    (hW : #W = Order.succ (2 ^ μ)) (hord : ord #W = typeLT W)
    (δ : W → W) (hδ : ∀ α ∈ bigCof μ, δ α < α) :
    ∃ δ₀, #W ≤ #{α | α ∈ bigCof μ ∧ δ α = δ₀} := by sorry
