-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_DualKernelLemmas_d1a
-- name    : Formalism.FourierDecayAlt.P.DualKernelLemmas.d1a
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T13:02:53.315363+00:00
-- url     : https://prove2.me/theorems/5b74f485-96d2-4ed1-9f4b-714c86b1f131
-- title:
--   Dual Kernel Lemmas: d1a
-- statement:
--   The Dual Kernel Lemmas construction uses the d1a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DualKernelLemmas.lean#L33-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DualKernelLemmas.lean#L33-L39

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GramProductIdentities
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagScalarCommuteOfEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PartialFlipCommuteDiagScalarOfFree
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagScalarCommuteTransposedRMatrix
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DualKernelLemmas
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.DualKernelLemmas
open Finset Formalism.FourierDecayAlt.FormPairingAction Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P.GramProductIdentities
open scoped Matrix

theorem Formalism.FourierDecayAlt.P.DualKernelLemmas.d1a : DualityPairingFormula := by sorry
