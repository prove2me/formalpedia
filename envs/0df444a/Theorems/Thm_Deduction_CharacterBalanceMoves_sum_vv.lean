-- Prove2me | Theorems.Thm_Deduction_CharacterBalanceMoves_sum_vv
-- name    : Deduction.CharacterBalanceMoves.sum_vv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:34:22.251796+00:00
-- url     : https://prove2.me/theorems/a1f2ed15-0f35-4879-9f06-5b5ef5b147f2
-- title:
--   Character Balance Moves: sum vv
-- statement:
--   The Character Balance Moves construction uses the sum vv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ChCore.lean#L187-L200
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ChCore.lean#L187-L200

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

theorem Deduction.CharacterBalanceMoves.sum_vv (A0 : AddSubgroup H) (Kp : Finset (AddChar (E0 × H) ℂ)) (hKp : ∀ ψ ∈ Kp, ψ ∈ PsiA A0)
    (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ) (c x : ℝ) :
    ∑ ψ ∈ PsiA A0, vv Kp D ell c x ψ = GmA D ell Kp c x - SigA D ell A0 Kp x := by sorry
