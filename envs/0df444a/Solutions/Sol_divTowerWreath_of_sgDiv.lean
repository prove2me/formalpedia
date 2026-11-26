-- Prove2me | solution 1 for divTowerWreath_of_sgDiv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:59:00.6924+00:00
-- url     : https://prove2.me/submissions/ae7106a0-795c-4c20-b058-bb5e51a65561

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
public import Theorems.Thm_KrohnRhodes_sgDiv_trans


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
theorem _root_.solution {S T : Type u} [Monoid S] [Finite S]
    [Monoid T] [Finite T] (h : SgDiv S T) :
    ∀ {factors : List KRFactor.{u}}, DivTowerWreath T factors →
      DivTowerWreath S factors := by
  intro factors
  cases factors with
  | nil =>
      intro hT
      rw [divTowerWreath_nil] at hT ⊢
      exact KrohnRhodes.sgDiv_trans h hT
  | cons F rest =>
      intro hT
      rw [divTowerWreath_cons] at hT ⊢
      obtain ⟨B, mB, fB, Y, fY, aY, hBrest, hTw⟩ := hT
      exact ⟨B, mB, fB, Y, fY, aY, hBrest,
        KrohnRhodes.sgDiv_trans h hTw⟩
