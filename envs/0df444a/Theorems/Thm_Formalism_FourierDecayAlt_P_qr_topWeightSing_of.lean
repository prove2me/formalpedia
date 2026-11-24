-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_qr_topWeightSing_of
-- name    : Formalism.FourierDecayAlt.P.qr_topWeightSing_of
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T17:28:17.159567+00:00
-- url     : https://prove2.me/theorems/f5cac04a-726c-42e1-934c-be774504bc2c
-- title:
--   P: qr top Weight Sing of
-- statement:
--   The P construction uses the qr top Weight Sing of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HighestWeightPolynomials.lean#L168-L199
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HighestWeightPolynomials.lean#L168-L199

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuantumMinorCommutation
import Definitions.Def_Lemmata_GeneralBFactSecondTerForm_Imports
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HighestWeightPolynomials
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr HighestWeightPolynomials

theorem Formalism.FourierDecayAlt.P.qr_topWeightSing_of (hX : Qr.ExistsSingMax) (hS : Qr.CapSing) : Qr.TopWeightSing := by sorry
