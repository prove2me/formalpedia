-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_CapelliAbstractCharacter_deg_prod_lin
-- name    : Formalism.FourierDecayAlt.P.CapelliAbstractCharacter.deg_prod_lin
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T18:54:56.27862+00:00
-- url     : https://prove2.me/theorems/bd903aea-e9f8-4887-9e78-8b9afceef7bb
-- title:
--   Capelli Abstract Character: deg prod lin
-- statement:
--   The Capelli Abstract Character construction uses the deg prod lin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CapelliAbstractCharacter.lean#L306-L309
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CapelliAbstractCharacter.lean#L306-L309

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

theorem Formalism.FourierDecayAlt.P.CapelliAbstractCharacter.deg_prod_lin {ι : Type} (S : Finset ι) (m : ι → ℂ) :
    (∏ j ∈ S, ((Polynomial.X : ℂ[X]) + C (m j))).natDegree ≤ S.card := by sorry
