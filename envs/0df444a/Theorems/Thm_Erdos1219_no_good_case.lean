-- Prove2me | Theorems.Thm_Erdos1219_no_good_case
-- name    : Erdos1219.no_good_case
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:43:18.117325+00:00
-- url     : https://prove2.me/theorems/7ef70e01-bc74-404a-9ee6-88780c14a069
-- title:
--   Erdos1219: no good case
-- statement:
--   Case 2: if no point is good, there is a `c`-homogeneous set of full cardinality.
--
--   Source: https://github.com/jbaelaw/erdos1219-lean/blob/00e696a9cd2bbd8cad33d2cdc90ad385058c1466/Erdos1219/UnbalancedErdosRado.lean#L207-L274
-- source:
--   https://github.com/jbaelaw/erdos1219-lean/blob/00e696a9cd2bbd8cad33d2cdc90ad385058c1466/Erdos1219/UnbalancedErdosRado.lean#L207-L274

import Definitions.Def_Erdos1219_Defs
import Mathlib.SetTheory.Cardinal.Pigeonhole
import Definitions.Def_Erdos1219_UnbalancedErdosRado
set_option autoImplicit false
open Cardinal Ordinal Set
open Erdos1219
universe u
variable {W : Type u} [LinearOrder W] [WellFoundedLT W]

theorem Erdos1219.no_good_case {f : W → W → Bool} (hf : ∀ x y, f x y = f y x) {c : Bool}
    {μ : Cardinal.{u}} (hμ : ℵ₀ ≤ μ) (hW : #W = Order.succ (2 ^ μ)) (hord : ord #W = typeLT W)
    (hno : ∀ α, ¬ IsGood f c μ α) : ∃ H : Set W, #H = #W ∧ Homog f c H := by sorry
