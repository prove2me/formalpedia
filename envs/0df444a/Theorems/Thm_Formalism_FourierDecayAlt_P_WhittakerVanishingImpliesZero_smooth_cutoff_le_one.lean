-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_WhittakerVanishingImpliesZero_smooth_cutoff_le_one
-- name    : Formalism.FourierDecayAlt.P.WhittakerVanishingImpliesZero.smooth_cutoff_le_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:35:57.889063+00:00
-- url     : https://prove2.me/theorems/b23b9b0e-31d6-41b2-8075-2e3725072811
-- title:
--   Whittaker Vanishing Implies Zero: smooth cutoff le one
-- statement:
--   The Whittaker Vanishing Implies Zero construction uses the smooth cutoff le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WhittakerVanishingImpliesZero.lean#L18-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WhittakerVanishingImpliesZero.lean#L18-L18

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

theorem Formalism.FourierDecayAlt.P.WhittakerVanishingImpliesZero.smooth_cutoff_le_one (r : ℝ) : chi0 r ≤ 1 := by sorry
