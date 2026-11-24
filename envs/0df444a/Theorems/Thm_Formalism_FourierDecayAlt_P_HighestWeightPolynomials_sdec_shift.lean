-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_HighestWeightPolynomials_sdec_shift
-- name    : Formalism.FourierDecayAlt.P.HighestWeightPolynomials.sdec_shift
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T17:28:58.664729+00:00
-- url     : https://prove2.me/theorems/6eba882d-16ca-41de-8313-1c6252cb4e88
-- title:
--   Highest Weight Polynomials: sdec shift
-- statement:
--   The Highest Weight Polynomials construction uses the sdec shift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HighestWeightPolynomials.lean#L41-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HighestWeightPolynomials.lean#L41-L51

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

theorem Formalism.FourierDecayAlt.P.HighestWeightPolynomials.sdec_shift {n : ℕ} {ν : Fin n → ℂ} (h : ∀ a b : Fin n, a < b → ∃ N : ℕ, ν a - ν b = (N : ℂ)) :
    SDec fun k => ν k - ((k : ℕ) : ℂ) := by sorry
