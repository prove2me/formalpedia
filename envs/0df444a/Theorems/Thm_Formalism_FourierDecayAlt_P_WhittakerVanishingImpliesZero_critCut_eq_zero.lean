-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_WhittakerVanishingImpliesZero_critCut_eq_zero
-- name    : Formalism.FourierDecayAlt.P.WhittakerVanishingImpliesZero.critCut_eq_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:35:41.33859+00:00
-- url     : https://prove2.me/theorems/4123ac29-04a5-4c9f-b19d-7b9721edff5b
-- title:
--   Whittaker Vanishing Implies Zero: crit Cut eq zero
-- statement:
--   The Whittaker Vanishing Implies Zero construction uses the crit Cut eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WhittakerVanishingImpliesZero.lean#L112-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WhittakerVanishingImpliesZero.lean#L112-L117

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

theorem Formalism.FourierDecayAlt.P.WhittakerVanishingImpliesZero.critCut_eq_zero {n : ℕ} {δ : ℝ} {z : ℂ} {x : Fin n → ℂ} (hδ : 0 < δ)
    (h : 2 * δ ≤ ‖x - fun _ => z‖) : critCut δ z x = 0 := by sorry
