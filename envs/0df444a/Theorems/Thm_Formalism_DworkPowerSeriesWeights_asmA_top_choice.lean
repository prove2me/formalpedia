-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_asmA_top_choice
-- name    : Formalism.DworkPowerSeriesWeights.asmA_top_choice
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:55:45.753643+00:00
-- url     : https://prove2.me/theorems/2e2c0e26-0175-4317-8754-5dcc8a3a269e
-- title:
--   Dwork Power Series Weights: asm A top choice
-- statement:
--   The Dwork Power Series Weights construction uses the asm A top choice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/CapacityLeReachCapacity.lean#L81-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/CapacityLeReachCapacity.lean#L81-L118

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

theorem Formalism.DworkPowerSeriesWeights.asmA_top_choice (l : ℕ) (hl : 2 ≤ l) (A : ℝ) (cap h : ℕ → ℝ)
    (hcap : ∀ j, 0 ≤ cap j) (hh : ∀ e, 0 ≤ h e) (hsum : Summable h) (R : Finset ℕ) (D : ℕ∞)
    (hRodd : ∀ j ∈ R, Odd j)
    (hmin : ∀ e : ℕ, Odd e → (e : ℕ∞) < D → min (A / (l : ℝ) ^ e) (cap e) ≤ h e)
    (hD : ∀ e : ℕ, D = e → A / (l : ℝ) ^ e ≤ h e) :
    ∃ ε : ℝ, 0 ≤ ε ∧ (∀ e : ℕ, D = e → ((l : ℝ) ^ e)⁻¹ ≤ ε) ∧
      A * ε + ∑ j ∈ R, cap j * max (1 - (l : ℝ) ^ j * ε) 0 ≤ ∑' e, h e := by sorry
