-- Prove2me | Theorems.Thm_Deduction_CharacterBalanceMoves_th_le
-- name    : Deduction.CharacterBalanceMoves.th_le
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T09:34:07.132524+00:00
-- url     : https://prove2.me/theorems/4303b4be-f5a6-420d-88bf-27437d9a2f63
-- title:
--   Character Balance Moves: th le
-- statement:
--   The Character Balance Moves construction uses the th le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ChCore.lean#L75-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ChCore.lean#L75-L152

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

theorem Deduction.CharacterBalanceMoves.th_le (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ) (T2 : Finset H) (x b b' η X' θ A : ℝ) (u0 t : H) (w : E0 × H → ℝ)
    (hx : 3 ≤ x) (hb : 0 < b) (hη : 0 ≤ η) (hX' : 0 < X') (_hb' : 0 < b') (hbX : b' * X' ≤ x * b) (hθ : 0 ≤ θ)
    (hA : |A / b - x| ≤ 1) (hwpos : ∀ ρ, InPhi ρ → 0 < w ρ)
    (hwthick : ∀ ρ, IsThickAt T2 u0 ρ → b ≤ w ρ ∧ w ρ ≤ b + η + 1)
    (hwthin : ∀ ρ, InPhi ρ → ¬ IsThickAt T2 u0 ρ → w ρ ≤ 2 * b')
    (hThin : ThinScales D ell X' θ) (hLip : LipW D ell) :
    (Th D ell T2 b (A / b) u0 t).re ≤ (De D ell A t w).re + 2 * fPl H * (3 * (x + 1) * (η + 1) + (x + 1) * b * θ) := by sorry
