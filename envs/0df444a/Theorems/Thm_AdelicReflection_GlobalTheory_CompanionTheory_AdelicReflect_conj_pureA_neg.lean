-- Prove2me | Theorems.Thm_AdelicReflection_GlobalTheory_CompanionTheory_AdelicReflect_conj_pureA_neg
-- name    : AdelicReflection.GlobalTheory.CompanionTheory.AdelicReflect.conj_pureA_neg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:54:20.004551+00:00
-- url     : https://prove2.me/theorems/0f499078-37d0-4a30-96c3-53469a8e9db3
-- title:
--   Adelic Reflect: conj pure A neg
-- statement:
--   The Adelic Reflect construction uses the conj pure A neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AdelicSchwartzSpaceClosedUnderConjReflection.lean#L32-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AdelicSchwartzSpaceClosedUnderConjReflection.lean#L32-L41

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

theorem AdelicReflection.GlobalTheory.CompanionTheory.AdelicReflect.conj_pureA_neg (F : Type) [Field F] [NumberField F] {κ : Type}
    (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ)
    (x : κ → AdeleRing (𝓞 F) F) :
    starRingEnd ℂ (GlobalTheory.WeilM.pureA F f g (-x)) =
      GlobalTheory.WeilM.pureA F (fun y => starRingEnd ℂ (f (-y))) (fun y => starRingEnd ℂ (g (-y))) x := by sorry
