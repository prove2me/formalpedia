-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_WhittakerVanishingImpliesZero_lt_two_mul_of_sq_div_lt
-- name    : Formalism.FourierDecayAlt.P.WhittakerVanishingImpliesZero.lt_two_mul_of_sq_div_lt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:36:00.467838+00:00
-- url     : https://prove2.me/theorems/36e02190-381e-4f3b-ae7d-4a57610cc279
-- title:
--   Whittaker Vanishing Implies Zero: lt two mul of sq div lt
-- statement:
--   The Whittaker Vanishing Implies Zero construction uses the lt two mul of sq div lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WhittakerVanishingImpliesZero.lean#L23-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WhittakerVanishingImpliesZero.lean#L23-L26

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RemainderNormLeStrictUpper
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WhittakerVanishingImpliesZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.WhittakerVanishingImpliesZero
open Formalism.FourierDecayAlt.G

theorem Formalism.FourierDecayAlt.P.WhittakerVanishingImpliesZero.lt_two_mul_of_sq_div_lt {a τ : ℝ} (ha : 0 ≤ a) (hτ : 0 < τ) (h : a ^ 2 / τ ^ 2 < 2) :
    a < 2 * τ := by sorry
