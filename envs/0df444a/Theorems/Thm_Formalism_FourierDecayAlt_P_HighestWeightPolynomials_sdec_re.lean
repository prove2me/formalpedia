-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_HighestWeightPolynomials_sdec_re
-- name    : Formalism.FourierDecayAlt.P.HighestWeightPolynomials.sdec_re
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T17:28:37.503822+00:00
-- url     : https://prove2.me/theorems/e327439d-591b-4fc5-9856-4e34fb7dd1ac
-- title:
--   Highest Weight Polynomials: sdec re
-- statement:
--   The Highest Weight Polynomials construction uses the sdec re property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HighestWeightPolynomials.lean#L28-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HighestWeightPolynomials.lean#L28-L35

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HighestWeightPolynomials
open Formalism.REAL Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr

theorem Formalism.FourierDecayAlt.P.HighestWeightPolynomials.sdec_re {n : ℕ} {m : Fin n → ℂ} (hm : SDec m) : StrictAnti fun a => (m a).re := by sorry
