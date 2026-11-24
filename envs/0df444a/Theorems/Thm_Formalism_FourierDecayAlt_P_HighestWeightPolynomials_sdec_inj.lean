-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_HighestWeightPolynomials_sdec_inj
-- name    : Formalism.FourierDecayAlt.P.HighestWeightPolynomials.sdec_inj
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T17:28:36.949271+00:00
-- url     : https://prove2.me/theorems/f7f335e3-c13f-4cdc-82bd-35b087f40a59
-- title:
--   Highest Weight Polynomials: sdec inj
-- statement:
--   The Highest Weight Polynomials construction uses the sdec inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HighestWeightPolynomials.lean#L37-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HighestWeightPolynomials.lean#L37-L39

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

theorem Formalism.FourierDecayAlt.P.HighestWeightPolynomials.sdec_inj {n : ℕ} {m : Fin n → ℂ} (hm : SDec m) : Function.Injective m := by sorry
