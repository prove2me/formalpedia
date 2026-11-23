-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_WhittakerVanishingImpliesZero_exists_lower
-- name    : Formalism.FourierDecayAlt.P.WhittakerVanishingImpliesZero.exists_lower
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:35:53.678722+00:00
-- url     : https://prove2.me/theorems/d3e32db2-1fa3-4ec7-b12a-c1e6a585046e
-- title:
--   Whittaker Vanishing Implies Zero: exists lower
-- statement:
--   The Whittaker Vanishing Implies Zero construction uses the exists lower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WhittakerVanishingImpliesZero.lean#L183-L188
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WhittakerVanishingImpliesZero.lean#L183-L188

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

theorem Formalism.FourierDecayAlt.P.WhittakerVanishingImpliesZero.exists_lower {Kc : Set ℂ} (hK : IsCompact Kc) (h0 : (0 : ℂ) ∉ Kc) :
    ∃ d : ℝ, 0 < d ∧ ∀ D ∈ Kc, d ≤ ‖D‖ := by sorry
