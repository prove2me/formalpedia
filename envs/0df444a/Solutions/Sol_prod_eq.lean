-- Prove2me | solution 1 for prod_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:22:28.35092+00:00
-- url     : https://prove2.me/submissions/fc6ec7e9-e2db-4b69-ac02-eaf2c3681be6

module
public import Mathlib.Util.Notation3
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Pair

set_option autoImplicit true
@[expose] public section
public section
open scoped ZhangYeungPFR
theorem _root_.solution {Ω S T : Type*} {X : Ω → S} {Y : Ω → T} {ω : Ω} :
    (⟨ X, Y ⟩ : Ω → S × T) ω = (X ω, Y ω) := rfl
