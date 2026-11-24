-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_CapelliAbstractCharacter_eval_prod_lin
-- name    : Formalism.FourierDecayAlt.P.CapelliAbstractCharacter.eval_prod_lin
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T18:55:06.594632+00:00
-- url     : https://prove2.me/theorems/54b1fd23-97af-4f9a-b0eb-38568beac811
-- title:
--   Capelli Abstract Character: eval prod lin
-- statement:
--   The Capelli Abstract Character construction uses the eval prod lin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CapelliAbstractCharacter.lean#L302-L304
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CapelliAbstractCharacter.lean#L302-L304

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuantumMinorCommutation
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CapelliAbstractCharacter
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Polynomial
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CapelliAbstractCharacter
open Formalism.REAL Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr

theorem Formalism.FourierDecayAlt.P.CapelliAbstractCharacter.eval_prod_lin {ι : Type} (S : Finset ι) (m : ι → ℂ) (u : ℂ) :
    (∏ j ∈ S, ((Polynomial.X : ℂ[X]) + C (m j))).eval u = ∏ j ∈ S, (u + m j) := by sorry
