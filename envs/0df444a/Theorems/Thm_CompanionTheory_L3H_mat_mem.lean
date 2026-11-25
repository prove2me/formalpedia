-- Prove2me | Theorems.Thm_CompanionTheory_L3H_mat_mem
-- name    : CompanionTheory.L3H.mat_mem
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T06:05:47.690676+00:00
-- url     : https://prove2.me/theorems/1a2c167d-a622-5fd5-be27-e46a7d6e5d95
-- title:
--   L3 H: mat mem
-- statement:
--   The L3 H construction uses the mat mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/HeckeStandardModules/InvMemRl.lean#L15-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/HeckeStandardModules/InvMemRl.lean#L15-L17

import Definitions.Def_CompanionTheory_AutomorphicTheory_HeckeStandardModules_IntegralOfModule
import Definitions.Def_CompanionTheory_AutomorphicTheory_HeckeStandardModules_InvMemRl
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.UG Formalism.L2 CompanionTheory.Split CompanionTheory.HeckeA
noncomputable section
open CompanionTheory CompanionTheory.L3H
variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]
local notation3 "L⁺" => maximalRealSubfield L

theorem CompanionTheory.L3H.mat_mem {S : Subring (AL L)} {A B : Matrix (Fin n) (Fin n) (AL L)} (hA : ∀ i j, A i j ∈ S) (hB : ∀ i j, B i j ∈ S)
    (i j : Fin n) : (A * B) i j ∈ S := by sorry
