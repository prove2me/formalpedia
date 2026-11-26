-- Prove2me | solution 1 for divTowerWreath_cons
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:58:01.869963+00:00
-- url     : https://prove2.me/submissions/06124680-21c9-435c-83a5-c6e8f70fcab3

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
theorem _root_.solution (M : Type u) [Monoid M] [Finite M]
    (F : KRFactor.{u}) (rest : List KRFactor.{u}) :
    DivTowerWreath M (F :: rest) ↔
      ∃ (B : Type u) (_ : Monoid B) (_ : Finite B)
        (Y : Type u) (_ : Fintype Y) (_ : MulAction B Y),
        DivTowerWreath B rest ∧
        SgDiv M (WreathProduct F.carrier B Y) := Iff.rfl
