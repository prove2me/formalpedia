-- Prove2me | Theorems.Thm_Erdos1219_good_case
-- name    : Erdos1219.good_case
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:43:11.206558+00:00
-- url     : https://prove2.me/theorems/b050a92f-b1c0-43d7-bb5e-2694fabd513e
-- title:
--   Erdos1219: good case
-- statement:
--   Case 1: a good point yields a `!c`-homogeneous set of size `μ⁺`.
--
--   Source: https://github.com/jbaelaw/erdos1219-lean/blob/00e696a9cd2bbd8cad33d2cdc90ad385058c1466/Erdos1219/UnbalancedErdosRado.lean#L108-L130
-- source:
--   https://github.com/jbaelaw/erdos1219-lean/blob/00e696a9cd2bbd8cad33d2cdc90ad385058c1466/Erdos1219/UnbalancedErdosRado.lean#L108-L130

import Definitions.Def_Erdos1219_Defs
import Mathlib.SetTheory.Cardinal.Pigeonhole
import Definitions.Def_Erdos1219_UnbalancedErdosRado
set_option autoImplicit false
open Cardinal Ordinal Set
open Erdos1219
universe u
variable {W : Type u} [LinearOrder W] [WellFoundedLT W]
omit [WellFoundedLT W]

theorem Erdos1219.good_case {f : W → W → Bool} (hf : ∀ x y, f x y = f y x) {c : Bool}
    {μ : Cardinal.{u}} {α : W} (hgood : IsGood f c μ α) :
    ∃ H : Set W, #H = Order.succ μ ∧ Homog f (!c) H := by sorry
