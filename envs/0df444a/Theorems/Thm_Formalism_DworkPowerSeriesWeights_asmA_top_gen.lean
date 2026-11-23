-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_asmA_top_gen
-- name    : Formalism.DworkPowerSeriesWeights.asmA_top_gen
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:54:09.120006+00:00
-- url     : https://prove2.me/theorems/062e75ae-bae2-46e9-9b5a-078fb26432e7
-- title:
--   Dwork Power Series Weights: asm A top gen
-- statement:
--   The Dwork Power Series Weights construction uses the asm A top gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/CapacityLeReachCapacity.lean#L126-L186
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/CapacityLeReachCapacity.lean#L126-L186

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

theorem Formalism.DworkPowerSeriesWeights.asmA_top_gen (l : ℕ) (hl : 2 ≤ l) (A : ℝ) (hA : 0 ≤ A) (cap : ℕ → ℝ)
    (hcap : ∀ j, 0 ≤ cap j) (D : ℕ∞) (hDodd : ∀ e : ℕ, D = e → Odd e) (R : Finset ℕ)
    (hR : ∀ j ∈ R, Odd j) :
    ∃ ε : ℝ, 0 ≤ ε ∧ (∀ e : ℕ, D = e → ((l : ℝ) ^ e)⁻¹ ≤ ε) ∧
      (∑' e, asmA_f l A cap D e) + (A * ε + ∑ j ∈ R, cap j * max (1 - (l : ℝ) ^ j * ε) 0) ≤
        A * gam l := by sorry
