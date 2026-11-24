-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_HighestWeightPolynomials_sdec_shf
-- name    : Formalism.FourierDecayAlt.P.HighestWeightPolynomials.sdec_shf
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T17:29:30.022656+00:00
-- url     : https://prove2.me/theorems/64b46c84-9ba2-453d-8b63-fb1b38e7e3de
-- title:
--   Highest Weight Polynomials: sdec shf
-- statement:
--   The Highest Weight Polynomials construction uses the sdec shf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HighestWeightPolynomials.lean#L53-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HighestWeightPolynomials.lean#L53-L63

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

theorem Formalism.FourierDecayAlt.P.HighestWeightPolynomials.sdec_shf {n : ℕ} (β : ℂ) {M : Fin n → ℤ} (hM : StrictAnti M) : SDec (shf β M) := by sorry
