-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_RealWeightedForms_first_polynomial_size_of_parts
-- name    : Formalism.FourierDecayAlt.P.RealWeightedForms.first_polynomial_size_of_parts
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T13:18:54.23287+00:00
-- url     : https://prove2.me/theorems/51a13eb8-9d37-4db3-88d8-4b1733ad0c34
-- title:
--   Real Weighted Forms: first polynomial size of parts
-- statement:
--   The Real Weighted Forms construction uses the first polynomial size of parts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RealWeightedForms.lean#L214-L214
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RealWeightedForms.lean#L214-L214

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

theorem Formalism.FourierDecayAlt.P.RealWeightedForms.first_polynomial_size_of_parts : SizeBoundOfParts := by sorry
