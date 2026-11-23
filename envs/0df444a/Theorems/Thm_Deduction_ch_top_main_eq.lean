-- Prove2me | Theorems.Thm_Deduction_ch_top_main_eq
-- name    : Deduction.ch_top_main_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:35:11.395022+00:00
-- url     : https://prove2.me/theorems/5a70c6ec-ca12-4c80-886c-917033aa67b8
-- title:
--   Deduction: ch top main eq
-- statement:
--   The Deduction construction uses the ch top main eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ChTop.lean#L11-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ChTop.lean#L11-L35

import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_SplitInertia
import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_ChTop
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

theorem Deduction.ch_top_main_eq {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] {U0 : Type} [Fintype U0] {W : U0 → Type}
    [∀ u0, Fintype (W u0)] [∀ u0, Nonempty (W u0)]
    {Top : Type} [Fintype Top] {m f : ℕ} (Dd : Data U0 W Top m f) (tr : U0 → H) (D : ArithData H) (N : ℕ)
    (ell : AddChar (E0 × H) ℂ → ℂ) (TT : Finset H) (a : H → ℝ) (w : H → Fin m → E0 × H → ℝ)
    (eT : Top ≃ TT) (eP : Fin f ≃ PhiSet (H := H)) (hId : IdentU Dd tr D N ell TT a w eT eP) (u0 : U0) :
    Dd.Main u0 = ∑ t ∈ TT, ∑ j : Fin m, (MAIN ell (a t) (w (tr u0) j)).re := by sorry
