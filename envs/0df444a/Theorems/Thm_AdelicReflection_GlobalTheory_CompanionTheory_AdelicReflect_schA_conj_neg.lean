-- Prove2me | Theorems.Thm_AdelicReflection_GlobalTheory_CompanionTheory_AdelicReflect_schA_conj_neg
-- name    : AdelicReflection.GlobalTheory.CompanionTheory.AdelicReflect.schA_conj_neg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:54:19.599606+00:00
-- url     : https://prove2.me/theorems/355607b7-011c-4144-a373-969a3f6661bd
-- title:
--   Adelic Reflect: sch A conj neg
-- statement:
--   The Adelic Reflect construction uses the sch A conj neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AdelicSchwartzSpaceClosedUnderConjReflection.lean#L43-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AdelicSchwartzSpaceClosedUnderConjReflection.lean#L43-L65

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AdelicSchwartzSpaceClosedUnderConjReflection
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AdelicReflection
open NumberField IsDedekindDomain
open scoped Classical
noncomputable section
open AdelicReflection.GlobalTheory AdelicReflection.GlobalTheory.CompanionTheory AdelicReflection.GlobalTheory.CompanionTheory.AdelicReflect

theorem AdelicReflection.GlobalTheory.CompanionTheory.AdelicReflect.schA_conj_neg : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ],
    ∀ φ ∈ GlobalTheory.WeilM.schA F κ, (fun x => starRingEnd ℂ (φ (-x))) ∈ GlobalTheory.WeilM.schA F κ := by sorry
