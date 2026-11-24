-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_herm_bvec_bvec
-- name    : Formalism.FourierDecayAlt.P.SignAntidiagonal.herm_bvec_bvec
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T20:36:15.328935+00:00
-- url     : https://prove2.me/theorems/76ad87b2-e49f-4a39-bcb9-5695acc0e65e
-- title:
--   Sign Antidiagonal: herm bvec bvec
-- statement:
--   The Sign Antidiagonal construction uses the herm bvec bvec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RightDerivativeRulePsi.lean#L31-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RightDerivativeRulePsi.lean#L31-L38

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainFirstIdentity
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RightDerivativeRulePsi
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.SignAntidiagonal
open Formalism.FourierDecayAlt.C3 Formalism.REAL Formalism.QuantumDeterminants

theorem Formalism.FourierDecayAlt.P.SignAntidiagonal.herm_bvec_bvec {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (p q : Fin n) :
    herm H (bvec p) (bvec q) = H q p := by sorry
