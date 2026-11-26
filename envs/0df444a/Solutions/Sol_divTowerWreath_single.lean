-- Prove2me | solution 1 for divTowerWreath_single
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:03:57.194465+00:00
-- url     : https://prove2.me/submissions/8bac5272-96c7-4133-a56d-bdfca7e24bf2

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
public import Theorems.Thm_divTowerWreath_cons
public import Theorems.Thm_sgDiv_wreath_subsingleton_base
public import Theorems.Thm_divTowerWreath_nil_of_subsingleton

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
theorem _root_.solution (F : KRFactor.{u}) :
    DivTowerWreath F.carrier [F] := by
  rw [divTowerWreath_cons]
  refine ⟨PUnit.{u + 1}, inferInstance, inferInstance, PUnit.{u + 1},
    inferInstance, inferInstance, divTowerWreath_nil_of_subsingleton PUnit.{u + 1}, ?_⟩
  exact sgDiv_wreath_subsingleton_base F.carrier PUnit.{u + 1}
