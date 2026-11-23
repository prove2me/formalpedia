-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_WhittakerVanishingImpliesZero_lt_of_critCut_ne_zero
-- name    : Formalism.FourierDecayAlt.P.WhittakerVanishingImpliesZero.lt_of_critCut_ne_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:36:20.58548+00:00
-- url     : https://prove2.me/theorems/888c15e3-39fb-43e1-a317-e8fbe27a1848
-- title:
--   Whittaker Vanishing Implies Zero: lt of crit Cut ne zero
-- statement:
--   The Whittaker Vanishing Implies Zero construction uses the lt of crit Cut ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WhittakerVanishingImpliesZero.lean#L106-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WhittakerVanishingImpliesZero.lean#L106-L110

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

theorem Formalism.FourierDecayAlt.P.WhittakerVanishingImpliesZero.lt_of_critCut_ne_zero {n : ℕ} {δ : ℝ} {z : ℂ} {x : Fin n → ℂ} (hδ : 0 < δ)
    (h : critCut δ z x ≠ 0) (k : Fin n) : ‖x k - z‖ < 2 * δ := by sorry
