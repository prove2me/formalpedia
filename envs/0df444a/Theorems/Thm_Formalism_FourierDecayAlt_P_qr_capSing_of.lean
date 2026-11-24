-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_qr_capSing_of
-- name    : Formalism.FourierDecayAlt.P.qr_capSing_of
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T17:29:15.876563+00:00
-- url     : https://prove2.me/theorems/c02b8a0b-dc99-4b8a-a069-cb9efdfa2bc5
-- title:
--   P: qr cap Sing of
-- statement:
--   The P construction uses the qr cap Sing of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HighestWeightPolynomials.lean#L158-L166
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HighestWeightPolynomials.lean#L158-L166

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

theorem Formalism.FourierDecayAlt.P.qr_capSing_of (hD : Qr.SingDom) (hX : Qr.ExistsSingMax) : Qr.CapSing := by sorry
