-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_WhittakerVanishingImpliesZero_norm_pow_sub_one_le
-- name    : Formalism.FourierDecayAlt.P.WhittakerVanishingImpliesZero.norm_pow_sub_one_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:50:49.484014+00:00
-- url     : https://prove2.me/theorems/a0876318-7bcb-4dde-a9c1-a7a756e5a92d
-- title:
--   Whittaker Vanishing Implies Zero: norm pow sub one le
-- statement:
--   The Whittaker Vanishing Implies Zero construction uses the norm pow sub one le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WhittakerVanishingImpliesZero.lean#L140-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WhittakerVanishingImpliesZero.lean#L140-L148

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

theorem Formalism.FourierDecayAlt.P.WhittakerVanishingImpliesZero.norm_pow_sub_one_le {ζ : ℂ} (h : ‖ζ‖ = 1) (i : ℕ) : ‖ζ ^ i - 1‖ ≤ i * ‖ζ - 1‖ := by sorry
