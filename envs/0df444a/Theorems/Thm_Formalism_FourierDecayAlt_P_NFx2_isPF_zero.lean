-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_isPF_zero
-- name    : Formalism.FourierDecayAlt.P.NFx2.isPF_zero
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T16:17:15.913154+00:00
-- url     : https://prove2.me/theorems/06a33f76-8eed-40e3-a45a-6944c7464542
-- title:
--   NFx2: is PF zero
-- statement:
--   The NFx2 construction uses the is PF zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ConnectionRaisingConstantEq.lean#L115-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ConnectionRaisingConstantEq.lean#L115-L131

import Definitions.Def_Formalism_HermitianCurvature_StatementNF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsPFSum
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConnectionRaisingConstantEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Polynomial
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.NFx2
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.NF
noncomputable section
variable {A : Type} [Ring A] [Algebra ℂ A]

theorem Formalism.FourierDecayAlt.P.NFx2.isPF_zero {f : ℂ → A} (hf : IsPF f) {S : Set ℂ} (hS : S.Infinite) (h0 : ∀ Y ∈ S, f Y = 0) :
    ∀ Y, f Y = 0 := by sorry
