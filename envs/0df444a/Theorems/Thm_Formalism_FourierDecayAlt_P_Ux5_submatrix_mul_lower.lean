-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Ux5_submatrix_mul_lower
-- name    : Formalism.FourierDecayAlt.P.Ux5.submatrix_mul_lower
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T16:29:22.167046+00:00
-- url     : https://prove2.me/theorems/2876d6cc-c7ba-48bb-9f68-0278c7599405
-- title:
--   Ux5: submatrix mul lower
-- statement:
--   The Ux5 construction uses the submatrix mul lower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/Block3MulBlocks.lean#L120-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/Block3MulBlocks.lean#L120-L138

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_DetNormLe
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Block3MulBlocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.QuantumDeterminants
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux5

theorem Formalism.FourierDecayAlt.P.Ux5.submatrix_mul_lower {p k : ℕ} (h : k ≤ p) (L X : Matrix (Fin p) (Fin p) ℂ)
    (hL : ∀ a b, a < b → L a b = 0) {l : Type*} (f : l → Fin p) :
    (L * X).submatrix (Fin.castLE h) f =
      L.submatrix (Fin.castLE h) (Fin.castLE h) * X.submatrix (Fin.castLE h) f := by sorry
