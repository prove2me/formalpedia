-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_HighestWeightPolynomials_hval_shift
-- name    : Formalism.FourierDecayAlt.P.HighestWeightPolynomials.hval_shift
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T17:28:17.90096+00:00
-- url     : https://prove2.me/theorems/0e3dda1b-c96c-4256-9043-824e0cbacb5c
-- title:
--   Highest Weight Polynomials: hval shift
-- statement:
--   The Highest Weight Polynomials construction uses the hval shift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HighestWeightPolynomials.lean#L65-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HighestWeightPolynomials.lean#L65-L78

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

theorem Formalism.FourierDecayAlt.P.HighestWeightPolynomials.hval_shift {n : ℕ} (ν : Fin n → ℂ) (a b : Fin n) :
    hval (fun c => ν c + (if c = a then 1 else 0) - (if c = b then 1 else 0)) =
      hval ν + (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ)) := by sorry
