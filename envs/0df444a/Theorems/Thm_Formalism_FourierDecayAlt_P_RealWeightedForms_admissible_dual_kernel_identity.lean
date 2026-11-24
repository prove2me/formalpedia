-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_RealWeightedForms_admissible_dual_kernel_identity
-- name    : Formalism.FourierDecayAlt.P.RealWeightedForms.admissible_dual_kernel_identity
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T13:19:30.0423+00:00
-- url     : https://prove2.me/theorems/2714921d-e452-4ff8-a587-9f4590d44d5b
-- title:
--   Real Weighted Forms: admissible dual kernel identity
-- statement:
--   The Real Weighted Forms construction uses the admissible dual kernel identity property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RealWeightedForms.lean#L112-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RealWeightedForms.lean#L112-L147

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

theorem Formalism.FourierDecayAlt.P.RealWeightedForms.admissible_dual_kernel_identity : AdmDK := by sorry
