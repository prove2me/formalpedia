-- Prove2me | Theorems.Thm_AdelicReflection_GlobalTheory_CompanionTheory_AdelicReflect_conjNeg_mem_SB
-- name    : AdelicReflection.GlobalTheory.CompanionTheory.AdelicReflect.conjNeg_mem_SB
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:54:28.653128+00:00
-- url     : https://prove2.me/theorems/e1e76edb-5e9f-46ff-a87c-04be6f3d2616
-- title:
--   Adelic Reflect: conj Neg mem SB
-- statement:
--   The Adelic Reflect construction uses the conj Neg mem SB property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AdelicSchwartzSpaceClosedUnderConjReflection.lean#L26-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AdelicSchwartzSpaceClosedUnderConjReflection.lean#L26-L30

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

theorem AdelicReflection.GlobalTheory.CompanionTheory.AdelicReflect.conjNeg_mem_SB {X : Type} [TopologicalSpace X] [AddGroup X] [IsTopologicalAddGroup X] {g : X → ℂ}
    (hg : g ∈ GlobalTheory.WeilM.SB X) : (fun y => starRingEnd ℂ (g (-y))) ∈ GlobalTheory.WeilM.SB X := by sorry
