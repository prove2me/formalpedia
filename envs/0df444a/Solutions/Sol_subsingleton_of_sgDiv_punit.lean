-- Prove2me | solution 1 for subsingleton_of_sgDiv_punit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:02:17.065532+00:00
-- url     : https://prove2.me/submissions/ad34ee2f-2713-48d9-88b2-c1f01cf1b20d

module
public import Definitions.Def_KrohnRhodes_Defs
public import Definitions.Def_KrohnRhodes_Foundations_WreathProduct
public import Definitions.Def_KrohnRhodes_Foundations_LocalDivisor
public import Definitions.Def_KrohnRhodes_Foundations_KrasnerKaloujnine
public import Definitions.Def_KrohnRhodes_Foundations_Division
public import Mathlib
public import Definitions.Def_KrohnRhodes_Foundations_MonoidWreathBridge
public import Definitions.Def_KrohnRhodes_Foundations_Cayley
public import Definitions.Def_KrohnRhodes_Foundations_ConstantMaps
public import Definitions.Def_KrohnRhodes_FactorTower

set_option autoImplicit true
@[expose] public section
public section
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false
set_option linter.style.show false
set_option linter.unusedSectionVars false
universe u
open Green
theorem _root_.solution (A : Type u) [Monoid A] [Finite A]
    (h : SgDiv A PUnit.{u + 1}) : Subsingleton A := by
  obtain ⟨U, φ, hφ⟩ := h
  constructor
  intro a b
  obtain ⟨ua, rfl⟩ := hφ a
  obtain ⟨ub, rfl⟩ := hφ b
  congr 1
  apply Subtype.ext
  apply Subsingleton.elim
