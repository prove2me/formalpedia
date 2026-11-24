-- Prove2me | Theorems.Thm_Erdos1219_not_good_unfold
-- name    : Erdos1219.not_good_unfold
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:43:11.504792+00:00
-- url     : https://prove2.me/theorems/42e13240-f695-4c2e-8e54-510bcf1624ee
-- title:
--   Erdos1219: not good unfold
-- statement:
--   The Erdos1219 construction uses the not good unfold property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jbaelaw/erdos1219-lean/blob/00e696a9cd2bbd8cad33d2cdc90ad385058c1466/Erdos1219/UnbalancedErdosRado.lean#L133-L140
-- source:
--   https://github.com/jbaelaw/erdos1219-lean/blob/00e696a9cd2bbd8cad33d2cdc90ad385058c1466/Erdos1219/UnbalancedErdosRado.lean#L133-L140

import Definitions.Def_Erdos1219_Defs
import Mathlib.SetTheory.Cardinal.Pigeonhole
import Definitions.Def_Erdos1219_UnbalancedErdosRado
set_option autoImplicit false
open Cardinal Ordinal Set
open Erdos1219
universe u
variable {W : Type u} [LinearOrder W] [WellFoundedLT W]
omit [WellFoundedLT W]

theorem Erdos1219.not_good_unfold {f : W → W → Bool} {c : Bool} {μ : Cardinal.{u}} {α : W}
    (hα : α ∈ bigCof μ) (hno : ¬ IsGood f c μ α) :
    ∃ (Z : Set W) (β : W), Z ⊆ nbr f c α ∧ Homog f (!c) Z ∧ #Z ≤ μ ∧ β < α ∧ Z ⊆ Iio β ∧
      nbr f c α ∩ common f c Z ⊆ Iio β := by sorry
