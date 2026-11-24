-- Prove2me | Theorems.Thm_Erdos1219_exists_seq
-- name    : Erdos1219.exists_seq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:43:08.138525+00:00
-- url     : https://prove2.me/theorems/ee2eefb0-5a27-44da-8998-d1ba88035e80
-- title:
--   Erdos1219: exists seq
-- statement:
--   Well-founded recursion: a sequence `β` indexed by a well-order `I` such that `β ξ` lies
--   above `h (β η)` for all `η < ξ`, provided all relevant sets are bounded.
--
--   Source: https://github.com/jbaelaw/erdos1219-lean/blob/00e696a9cd2bbd8cad33d2cdc90ad385058c1466/Erdos1219/UnbalancedErdosRado.lean#L47-L57
-- source:
--   https://github.com/jbaelaw/erdos1219-lean/blob/00e696a9cd2bbd8cad33d2cdc90ad385058c1466/Erdos1219/UnbalancedErdosRado.lean#L47-L57

import Definitions.Def_Erdos1219_Defs
import Mathlib.SetTheory.Cardinal.Pigeonhole
import Definitions.Def_Erdos1219_UnbalancedErdosRado
set_option autoImplicit false
open Cardinal Ordinal Set
open Erdos1219
universe u
variable {X : Type u} [LinearOrder X] [WellFoundedLT X]

theorem Erdos1219.exists_seq {I W : Type u} [LinearOrder I] [WellFoundedLT I] [LinearOrder W]
    [WellFoundedLT W] {κ : Cardinal.{u}}
    (hb : ∀ s : Set W, #s < κ → ∃ x, ∀ y ∈ s, y < x) (hI : ∀ ξ : I, #(Iio ξ) < κ)
    (h : W → W) : ∃ β : I → W, ∀ ξ η, η < ξ → h (β η) < β ξ := by sorry
