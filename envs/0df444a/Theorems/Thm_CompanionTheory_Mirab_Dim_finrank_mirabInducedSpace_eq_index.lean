-- Prove2me | Theorems.Thm_CompanionTheory_Mirab_Dim_finrank_mirabInducedSpace_eq_index
-- name    : CompanionTheory.Mirab.Dim.finrank_mirabInducedSpace_eq_index
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T18:26:11.543689+00:00
-- url     : https://prove2.me/theorems/190ee43f-53f6-47b3-b8e9-05582d413e2a
-- title:
--   Dim: finrank mirab Induced Space eq index
-- statement:
--   The Dim construction uses the finrank mirab Induced Space eq index property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/MirabolicRestriction/MirabolicInduction/IndDim.lean#L92-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/MirabolicRestriction/MirabolicInduction/IndDim.lean#L92-L97

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

theorem CompanionTheory.Mirab.Dim.finrank_mirabInducedSpace_eq_index (ψ₀ : AddChar k ℂ) :
    Module.finrank ℂ (MirabInducedSpace n ψ₀) = (uniSub k n).index := by sorry
