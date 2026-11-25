-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_RestrictedDualKernel_lemmaDKSub
-- name    : Formalism.FourierDecayAlt.P.RestrictedDualKernel.lemmaDKSub
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T13:19:09.510051+00:00
-- url     : https://prove2.me/theorems/20c7b78a-226c-4890-95e3-cd841239dead
-- title:
--   Restricted Dual Kernel: lemma DKSub
-- statement:
--   The Restricted Dual Kernel construction uses the lemma DKSub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RestrictedDualKernel.lean#L45-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RestrictedDualKernel.lean#L45-L63

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DualKernelLemmas
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RestrictedDualKernel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.RestrictedDualKernel
open Finset Formalism.FourierDecayAlt.FormPairingAction Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P.GramProductIdentities Formalism.FourierDecayAlt.P.DualKernelLemmas
open scoped Matrix ComplexOrder

theorem Formalism.FourierDecayAlt.P.RestrictedDualKernel.lemmaDKSub : LemmaDKSub := by sorry
