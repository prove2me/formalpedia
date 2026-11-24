-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_qr_decomp_of
-- name    : Formalism.FourierDecayAlt.P.qr_decomp_of
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T16:50:48.638611+00:00
-- url     : https://prove2.me/theorems/377b58d6-ca5a-4a76-a8cd-4746ec30f69f
-- title:
--   P: qr decomp of
-- statement:
--   The P construction uses the qr decomp of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BranchingSystems.lean#L256-L324
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BranchingSystems.lean#L256-L324

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuantumDetHighestWeightHolds
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BranchingSystems
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr BranchingSystems

theorem Formalism.FourierDecayAlt.P.qr_decomp_of : Qr.ExistsSingMax → Qr.CapSing → Qr.CapStab → Qr.SubRel → Qr.CovUp → Qr.VecDown →
    Qr.RaiseNZ → Qr.LowerNZ → Qr.Decomp := by sorry
