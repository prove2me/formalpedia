-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_prod_poly
-- name    : Formalism.FourierDecayAlt.P.SignAntidiagonal.prod_poly
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T20:52:11.937646+00:00
-- url     : https://prove2.me/theorems/61ec5bc7-459b-46d0-a1a1-6c5057e21ff9
-- title:
--   Sign Antidiagonal: prod poly
-- statement:
--   The Sign Antidiagonal construction uses the prod poly property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PlMonoConst.lean#L73-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PlMonoConst.lean#L73-L116

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RightDerivativeRulePsi
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PlMonoConst
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
variable {A : Type} [Ring A] [Algebra ℂ A]

theorem Formalism.FourierDecayAlt.P.SignAntidiagonal.prod_poly : ∀ (t : ℕ) (c δ : Fin t → ℂ) (F : Fin t → A),
    PolyLe t (fun u => (List.ofFn fun k => algebraMap ℂ A ((u + c k) * δ k) + F k).prod -
      algebraMap ℂ A (u ^ t * ∏ k, δ k)) := by sorry
