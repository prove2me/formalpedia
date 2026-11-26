-- Prove2me | solution 1 for divTowerWreath_nil_of_subsingleton
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:58:43.531237+00:00
-- url     : https://prove2.me/submissions/1498d795-4aad-4dc2-8a64-ce6488f79909

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
    [Subsingleton M] : DivTowerWreath M ([] : List KRFactor.{u}) := by
  rw [divTowerWreath_nil]
  -- `SgDiv M PUnit`: the top subsemigroup of `PUnit` maps onto `M` (which is a
  -- single point) by `_ ↦ 1`.
  refine ⟨⊤, ⟨fun _ => (1 : M), fun _ _ => Subsingleton.elim _ _⟩, ?_⟩
  intro m
  exact ⟨⟨PUnit.unit, Subsemigroup.mem_top _⟩, Subsingleton.elim _ _⟩
