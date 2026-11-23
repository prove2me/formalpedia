-- Prove2me | Theorems.Thm_Deduction_CharacterBalanceMoves_mem_psi
-- name    : Deduction.CharacterBalanceMoves.mem_psi
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:34:22.659941+00:00
-- url     : https://prove2.me/theorems/5b37271b-4330-45c3-8a94-23b74e153aaa
-- title:
--   Character Balance Moves: mem psi
-- statement:
--   The Character Balance Moves construction uses the mem psi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ChCore.lean#L22-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ChCore.lean#L22-L26

import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_SplitInertia
import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_ChBalance
import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_ChCore
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Deduction
open Deduction.CH Formalism Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.LChain
open Deduction.CharacterBalanceMoves
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]

theorem Deduction.CharacterBalanceMoves.mem_psi (A0 : AddSubgroup H) (ψ : AddChar (E0 × H) ℂ) : ψ ∈ PsiA A0 ↔ ∀ s ∈ A0, ψ (0, s) = 1 := by sorry
