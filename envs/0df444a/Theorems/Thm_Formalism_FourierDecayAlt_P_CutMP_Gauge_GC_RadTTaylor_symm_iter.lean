-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_RadTTaylor_symm_iter
-- name    : Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.RadTTaylor.symm_iter
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T07:18:21.226336+00:00
-- url     : https://prove2.me/theorems/e6a89f10-95eb-5f7b-8274-70b71d5bce6d
-- title:
--   Rad TTaylor: symm iter
-- statement:
--   The Rad TTaylor construction uses the symm iter property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutGCoreGTCLRadTTaylor.lean#L26-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutGCoreGTCLRadTTaylor.lean#L26-L116

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreGTCLRadTCut
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreGTCLRadTTaylor
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ContDiff
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.Gauge Formalism.FourierDecayAlt.P.CutMP.Gauge.GC Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.RadTTaylor
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.RadTTaylor.symm_iter : ∀ (n : ℕ) (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] (f : E → W) (U : Set E),
    IsOpen U → ContDiffOn ℝ ∞ f U → ∀ x ∈ U, ∀ (σ : Equiv.Perm (Fin n)) (v : Fin n → E),
      iteratedFDeriv ℝ n f x (v ∘ σ) = iteratedFDeriv ℝ n f x v := by sorry
