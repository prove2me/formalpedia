-- Prove2me | Theorems.Thm_CompanionTheory_Mirab_Dim_psiExt_of_mem
-- name    : CompanionTheory.Mirab.Dim.psiExt_of_mem
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T18:17:49.087091+00:00
-- url     : https://prove2.me/theorems/d09fe05c-59e6-415d-bb03-34b3b1ff5ecb
-- title:
--   Dim: psi Ext of mem
-- statement:
--   The Dim construction uses the psi Ext of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/MirabolicRestriction/MirabolicInduction/IndDim.lean#L38-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/MirabolicRestriction/MirabolicInduction/IndDim.lean#L38-L40

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_PublishedFoundations_BlockTriangularOfSubOne
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicIsMackey
import Definitions.Def_CompanionTheory_AutomorphicTheory_MirabolicRestriction_MirabolicInduction_IndDim
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.FiniteGL Formalism.L2.Indef.Tree Formalism.EigenvalueLevelCeiling
open CompanionTheory CompanionTheory.Mirab CompanionTheory.Mirab.Dim
variable {k : Type} [Field k] [Fintype k] (n : ℕ)
variable (ψ₀ : AddChar k ℂ)

theorem CompanionTheory.Mirab.Dim.psiExt_of_mem (u : uniSub k n) : psiExt n ψ₀ (u : mirabSub k n) = genericChar n ψ₀ u := by sorry
