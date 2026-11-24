-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_WhittakerVanishingImpliesZero_root_sep
-- name    : Formalism.FourierDecayAlt.P.WhittakerVanishingImpliesZero.root_sep
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:52:05.65839+00:00
-- url     : https://prove2.me/theorems/5845b856-ce1a-42f3-92f1-a0ca237ef7cb
-- title:
--   Whittaker Vanishing Implies Zero: root sep
-- statement:
--   The Whittaker Vanishing Implies Zero construction uses the root sep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WhittakerVanishingImpliesZero.lean#L169-L181
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WhittakerVanishingImpliesZero.lean#L169-L181

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

theorem Formalism.FourierDecayAlt.P.WhittakerVanishingImpliesZero.root_sep {s : ℕ} (hs : 0 < s) {z z' : ℂ} (h : z ^ s = z' ^ s) (hne : z ≠ z') :
    ‖z‖ ≤ (s : ℝ) * ‖z - z'‖ := by sorry
