-- Prove2me | Theorems.Thm_Erdos1219_homog_sUnion_of_chain
-- name    : Erdos1219.homog_sUnion_of_chain
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:43:07.7728+00:00
-- url     : https://prove2.me/theorems/ff38426d-c3f8-4d04-a0b5-69d6a4a75717
-- title:
--   Erdos1219: homog s Union of chain
-- statement:
--   The Erdos1219 construction uses the homog s Union of chain property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jbaelaw/erdos1219-lean/blob/00e696a9cd2bbd8cad33d2cdc90ad385058c1466/Erdos1219/UnbalancedErdosRado.lean#L85-L92
-- source:
--   https://github.com/jbaelaw/erdos1219-lean/blob/00e696a9cd2bbd8cad33d2cdc90ad385058c1466/Erdos1219/UnbalancedErdosRado.lean#L85-L92

import Definitions.Def_Erdos1219_Defs
import Mathlib.SetTheory.Cardinal.Pigeonhole
import Definitions.Def_Erdos1219_UnbalancedErdosRado
set_option autoImplicit false
open Cardinal Ordinal Set
open Erdos1219
universe u
variable {W : Type u} [LinearOrder W] [WellFoundedLT W]
omit [LinearOrder W] [WellFoundedLT W]

theorem Erdos1219.homog_sUnion_of_chain {f : W → W → Bool} {c : Bool} {ch : Set (Set W)}
    (hch : IsChain (· ⊆ ·) ch) (hh : ∀ Z ∈ ch, Homog f c Z) : Homog f c (⋃₀ ch) := by sorry
