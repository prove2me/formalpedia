-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_asmA_top_core
-- name    : Formalism.DworkPowerSeriesWeights.asmA_top_core
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:54:09.017426+00:00
-- url     : https://prove2.me/theorems/672f5562-2dc4-46de-bf06-52e0611dd753
-- title:
--   Dwork Power Series Weights: asm A top core
-- statement:
--   The Dwork Power Series Weights construction uses the asm A top core property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/CapacityLeReachCapacity.lean#L45-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/CapacityLeReachCapacity.lean#L45-L79

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_GaussJetBounds_StatementA
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_PadicValFactorialRatioProd
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_CapacityLeReachCapacity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.DworkPowerSeriesWeights
open Formalism.IncomingBounds

theorem Formalism.DworkPowerSeriesWeights.asmA_top_core (l : ℕ) (hl : 2 ≤ l) (A : ℝ) (cap h : ℕ → ℝ)
    (hcap : ∀ j, 0 ≤ cap j) (hh : ∀ e, 0 ≤ h e) (hsum : Summable h) (R : Finset ℕ) (T : ℕ)
    (hT : A / (l : ℝ) ^ T ≤ h T) (hR : ∀ j ∈ R, j < T → cap j ≤ h j) :
    A * ((l : ℝ) ^ T)⁻¹ + ∑ j ∈ R, cap j * max (1 - (l : ℝ) ^ j * ((l : ℝ) ^ T)⁻¹) 0 ≤
      ∑' e, h e := by sorry
