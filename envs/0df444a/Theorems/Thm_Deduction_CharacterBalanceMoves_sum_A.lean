-- Prove2me | Theorems.Thm_Deduction_CharacterBalanceMoves_sum_A
-- name    : Deduction.CharacterBalanceMoves.sum_A
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:34:35.167769+00:00
-- url     : https://prove2.me/theorems/036fa616-17ec-4e71-a9e5-6c476697a719
-- title:
--   Character Balance Moves: sum A
-- statement:
--   The Character Balance Moves construction uses the sum A property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ChCore.lean#L28-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ChCore.lean#L28-L54

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

theorem Deduction.CharacterBalanceMoves.sum_A (A0 : AddSubgroup H) [Fintype A0] (ψ : AddChar (E0 × H) ℂ) (s t : H) (hs : s ∈ A0) :
    ∑ u : A0, ψ (-(e1 (s + (u : H) - t))) = if ψ ∈ PsiA A0 then (Fintype.card A0 : ℂ) * ψ (e1 t) else 0 := by sorry
