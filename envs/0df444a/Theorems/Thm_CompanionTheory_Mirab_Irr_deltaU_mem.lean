-- Prove2me | Theorems.Thm_CompanionTheory_Mirab_Irr_deltaU_mem
-- name    : CompanionTheory.Mirab.Irr.deltaU_mem
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T18:12:04.165614+00:00
-- url     : https://prove2.me/theorems/096542a1-ce40-489e-b9fe-f5b39b8b15a4
-- title:
--   Irr: delta U mem
-- statement:
--   The Irr construction uses the delta U mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/MirabolicRestriction/MirabolicInduction/IndIrr.lean#L41-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/MirabolicRestriction/MirabolicInduction/IndIrr.lean#L41-L55

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_PublishedFoundations_BlockTriangularOfSubOne
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicIsMackey
import Definitions.Def_CompanionTheory_AutomorphicTheory_MirabolicRestriction_MirabolicInduction_IndIrr
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
open CompanionTheory CompanionTheory.Mirab CompanionTheory.Mirab.Irr
variable {k : Type} [Field k] [Fintype k] (n : ℕ)

theorem CompanionTheory.Mirab.Irr.deltaU_mem (ψ₀ : AddChar k ℂ) : deltaU n ψ₀ ∈ MirabInducedSpace n ψ₀ := by sorry
