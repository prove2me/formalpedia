-- Prove2me | solution 1 for sgDiv_wreath_of_subsingleton_decoration
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:02:23.321868+00:00
-- url     : https://prove2.me/submissions/1538bb1c-e936-4357-9d54-efacceecf148

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
theorem _root_.solution (A B X : Type u) [Monoid A]
    [Finite A] [Monoid B] [Finite B] [Fintype X] [MulAction B X] [Subsingleton A] :
    SgDiv (WreathProduct A B X) B := by
  refine ⟨⊤, ⟨fun b => ⟨fun _ => 1, b.1⟩, ?_⟩, ?_⟩
  · rintro ⟨a, -⟩ ⟨b, -⟩
    apply WreathProduct.ext
    · funext x; exact Subsingleton.elim _ _
    · rfl
  · intro w
    refine ⟨⟨w.base, Subsemigroup.mem_top _⟩, ?_⟩
    apply WreathProduct.ext
    · funext x; exact Subsingleton.elim _ _
    · rfl
