-- Prove2me | Theorems.Thm_CompanionTheory_Mirab_Dim_eq_at_rep
-- name    : CompanionTheory.Mirab.Dim.eq_at_rep
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T18:15:42.972418+00:00
-- url     : https://prove2.me/theorems/feca967b-1940-5394-bba8-58e9a7f6b513
-- title:
--   Dim: eq at rep
-- statement:
--   The Dim construction uses the eq at rep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/MirabolicRestriction/MirabolicInduction/IndDim.lean#L67-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/MirabolicRestriction/MirabolicInduction/IndDim.lean#L67-L72

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

theorem CompanionTheory.Mirab.Dim.eq_at_rep (f : MirabInducedSpace n ψ₀) (x : mirabSub k n) :
    (f : mirabSub k n → ℂ) x =
      genericChar n ψ₀ ⟨_, rep_mem n x⟩ * (f : mirabSub k n → ℂ) (rep n x) := by sorry
