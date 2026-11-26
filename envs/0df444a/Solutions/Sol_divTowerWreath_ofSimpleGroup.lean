-- Prove2me | solution 1 for divTowerWreath_ofSimpleGroup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:05:08.409503+00:00
-- url     : https://prove2.me/submissions/ea169eb6-cff8-4b59-a70b-7a5d3559f0d3

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
public import Theorems.Thm_divTowerWreath_single

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
theorem _root_.solution (G : Type u) [Group G] [Finite G]
    [IsSimpleGroup G] :
    DivTowerWreath G [KRFactor.ofSimpleGroup G] :=
  divTowerWreath_single (KRFactor.ofSimpleGroup G)
