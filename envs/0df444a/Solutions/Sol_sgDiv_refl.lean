-- Prove2me | solution 1 for sgDiv_refl
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:58:35.554831+00:00
-- url     : https://prove2.me/submissions/cd39f644-77b6-473e-b88f-be238ef89594

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
theorem _root_.solution (S : Type u) [Semigroup S] : SgDiv S S := by
  refine ⟨⊤, ⟨fun ⟨x, _⟩ => x, ?_⟩, ?_⟩
  · intro ⟨_, _⟩ ⟨_, _⟩; rfl
  · intro s; exact ⟨⟨s, Subsemigroup.mem_top s⟩, rfl⟩
