-- Prove2me | solution 1 for sgDiv_wreath_assoc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:03:13.827021+00:00
-- url     : https://prove2.me/submissions/69ee93d5-f339-4898-a7ac-ba4224ab8cda

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
public import Theorems.Thm_sgDiv_refl
public import Theorems.Thm_WreathAssoc_Phi_injective
public import Theorems.Thm_KrohnRhodes_sgDiv_of_injective_hom


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
theorem _root_.solution (G B' B Y X : Type u)
    [Monoid G] [Finite G] [Monoid B'] [Finite B']
    [Monoid B] [Finite B] [Fintype Y] [Fintype X]
    [MulAction B' Y] [MulAction B X] :
    letI := WreathAssoc.actW B' B Y X
    SgDiv (WreathProduct (WreathProduct G B' Y) B X)
          (WreathProduct G (WreathProduct B' B X) (Y × X)) := by
  let := WreathAssoc.actW B' B Y X
  exact KrohnRhodes.sgDiv_of_injective_hom (sgDiv_refl _)
    (WreathAssoc.Phi G B' B Y X) (WreathAssoc.Phi_injective G B' B Y X)
