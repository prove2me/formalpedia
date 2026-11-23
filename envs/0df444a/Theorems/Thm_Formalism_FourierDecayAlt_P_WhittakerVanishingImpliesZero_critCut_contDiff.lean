-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_WhittakerVanishingImpliesZero_critCut_contDiff
-- name    : Formalism.FourierDecayAlt.P.WhittakerVanishingImpliesZero.critCut_contDiff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:35:47.26072+00:00
-- url     : https://prove2.me/theorems/9bb89c0f-0e4b-44f3-be86-590b4d28c7a6
-- title:
--   Whittaker Vanishing Implies Zero: crit Cut cont Diff
-- statement:
--   The Whittaker Vanishing Implies Zero construction uses the crit Cut cont Diff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WhittakerVanishingImpliesZero.lean#L119-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WhittakerVanishingImpliesZero.lean#L119-L122

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

theorem Formalism.FourierDecayAlt.P.WhittakerVanishingImpliesZero.critCut_contDiff {d : ℕ} (δ : ℝ) (z : ℂ) {n : ℕ∞} : ContDiff ℝ n (critCut (n := d) δ z) := by sorry
