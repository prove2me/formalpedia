-- Prove2me | Theorems.Thm_CompanionTheory_Mirab_Dim_psiExt_mul
-- name    : CompanionTheory.Mirab.Dim.psiExt_mul
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T18:18:36.175802+00:00
-- url     : https://prove2.me/theorems/44f20f82-6209-4c98-8438-d51f2c0293ad
-- title:
--   Dim: psi Ext mul
-- statement:
--   The Dim construction uses the psi Ext mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/MirabolicRestriction/MirabolicInduction/IndDim.lean#L42-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/MirabolicRestriction/MirabolicInduction/IndDim.lean#L42-L46

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

theorem CompanionTheory.Mirab.Dim.psiExt_mul (u : uniSub k n) (y : mirabSub k n) (hy : y ∈ uniSub k n) :
    psiExt n ψ₀ ((u : mirabSub k n) * y) = genericChar n ψ₀ u * psiExt n ψ₀ y := by sorry
