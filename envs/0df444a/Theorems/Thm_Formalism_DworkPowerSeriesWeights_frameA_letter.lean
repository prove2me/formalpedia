-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_frameA_letter
-- name    : Formalism.DworkPowerSeriesWeights.frameA_letter
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:00:17.893127+00:00
-- url     : https://prove2.me/theorems/1ce4d464-9ee5-4967-bd04-bc9c4e7e5b57
-- title:
--   Dwork Power Series Weights: frame A letter
-- statement:
--   The Dwork Power Series Weights construction uses the frame A letter property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/FrameA.lean#L48-L194
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/FrameA.lean#L48-L194

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_GaussJetBounds_StatementK
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_NormDetLeOneOfEntries
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_FrameA
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
universe u
open Formalism Formalism.DworkPowerSeriesWeights
open Formalism.IncomingBounds

theorem Formalism.DworkPowerSeriesWeights.frameA_letter {K : Type u} [NormedField K] [IsUltrametricDist K] (J N0 : ℕ)
    (lam : Fin J → Fin N0 → K) (y : Fin N0 → Fin N0 → K) (hlam : ∀ i a, ‖lam i a‖ ≤ 1)
    (hy : ∀ k a, ‖y k a‖ ≤ 1) (e : Fin J → Fin N0) (he : Function.Injective e)
    (top : Fin N0 → Prop) [DecidablePred top] (htop : ∀ i, ¬ top (e i))
    (hdet : ‖(Matrix.of fun (i i' : Fin J) => ∑ a, lam i a * y (e i') a).det‖ = 1) :
    ∃ (x T : Fin N0 → Fin N0 → K), (∀ k a, ‖x k a‖ ≤ 1) ∧ (∀ i k, ‖T i k‖ ≤ 1) ∧
      (∀ k a, top k → x k a = y k a) ∧
      (∀ i a, ¬ top i → y i a = ∑ k, (if top k then 0 else T i k) * x k a) ∧
      (∀ i k, ¬ top k → k ≠ e i → ∑ a, lam i a * x k a = 0) := by sorry
