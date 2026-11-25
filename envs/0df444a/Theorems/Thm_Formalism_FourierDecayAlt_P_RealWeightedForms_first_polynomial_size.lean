-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_RealWeightedForms_first_polynomial_size
-- name    : Formalism.FourierDecayAlt.P.RealWeightedForms.first_polynomial_size
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T13:18:59.346385+00:00
-- url     : https://prove2.me/theorems/d50d500d-986c-4582-99a1-3b82a2882fab
-- title:
--   Real Weighted Forms: first polynomial size
-- statement:
--   The Real Weighted Forms construction uses the first polynomial size property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RealWeightedForms.lean#L211-L212
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RealWeightedForms.lean#L211-L212

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DualKernelLemmas
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RealWeightedForms
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.RealWeightedForms
open Finset Formalism.FourierDecayAlt.FormPairingAction Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P.GramProductIdentities Formalism.FourierDecayAlt.P.DualKernelLemmas
open scoped Matrix

theorem Formalism.FourierDecayAlt.P.RealWeightedForms.first_polynomial_size : AdmissiblePointSizeBound := by sorry
