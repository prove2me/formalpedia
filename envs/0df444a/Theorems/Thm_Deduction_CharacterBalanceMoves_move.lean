-- Prove2me | Theorems.Thm_Deduction_CharacterBalanceMoves_move
-- name    : Deduction.CharacterBalanceMoves.move
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:34:11.400805+00:00
-- url     : https://prove2.me/theorems/bc9a51f4-2921-4455-90bb-962719484017
-- title:
--   Character Balance Moves: move
-- statement:
--   The Character Balance Moves construction uses the move property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ChCore.lean#L154-L165
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ChCore.lean#L154-L165

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

theorem Deduction.CharacterBalanceMoves.move (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ) {x Cd y : ℝ} (hx : 3 ≤ x) (hCd : 0 ≤ Cd)
    (hy : |y - x| ≤ 1) (hDer : DerivInt D ell Cd) (ψ : AddChar (E0 × H) ℂ) (hψ0 : ψ ≠ 0) :
    ‖GPsi D ell ψ y - GPsi D ell ψ x‖ ≤ Real.log (x + 1) + Cd + ‖ell ψ‖ := by sorry
