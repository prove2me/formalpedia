-- Prove2me | Theorems.Thm_Deduction_ch_core
-- name    : Deduction.ch_core
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:35:27.016624+00:00
-- url     : https://prove2.me/theorems/3ee8ec9b-c992-4ec7-8344-bfa1f33689ca
-- title:
--   Deduction: ch core
-- statement:
--   The Deduction construction uses the ch core property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ChCore.lean#L343-L442
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ChCore.lean#L343-L442

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
set_option maxHeartbeats 1600000

theorem Deduction.ch_core (C ε CE Ko c M : ℝ) (hC : 0 ≤ C) (hε : 0 < ε) (hc : |c| ≤ 1) : ∃ x1 : ℝ, ∀ x ≥ x1,
    ∀ (H : Type) [AddCommGroup H] [Fintype H] [DecidableEq H] (m : ℕ) (D : ArithData H) (S : Finset ℕ)
      (ell : AddChar (E0 × H) ℂ → ℂ) (N : ℕ) (TT T2 : Finset H) (a : H → ℝ) (w : H → Fin m → E0 × H → ℝ)
      (b b' k aE η X' θ : ℝ) (A0 : AddSubgroup H) (Kp : Finset (AddChar (E0 × H) ℂ)),
      HostFactsS D S → 0 < b → 0 ≤ aE → 0 < k → (m : ℝ) ≤ x ^ ((1 : ℝ) / 2 + ε / 2) → x * m ≤ k →
      SizesA A0 TT T2 a w N x b b' η X' θ → ThinScales D ell X' θ → CostWindows x (fPl H) b η θ →
      RestSize ε x (Fintype.card H) TT.card T2.card m b k aE → (∀ s ∈ T2, s ∈ A0) → CharsA ell A0 Kp TT c M Ko CE ε x →
      (∀ u ∈ A0, gapA D N ell TT a w u ≤ x ^ (C * ε) * errorBracketSizeWindows x ε (Fintype.card H) TT.card T2.card m b k aE) →
      GmA D ell Kp c x ≤ x ^ ((1 : ℝ) / 2 + (C + 3) * ε) + SigA D ell A0 Kp x := by sorry
