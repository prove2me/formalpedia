-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_isPF_eq
-- name    : Formalism.FourierDecayAlt.P.NFx2.isPF_eq
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T15:12:53.318372+00:00
-- url     : https://prove2.me/theorems/c90b0eb4-80e3-4105-a7ce-bccf5bf97bbf
-- title:
--   NFx2: is PF eq
-- statement:
--   The NFx2 construction uses the is PF eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ConnectionRaisingConstantEq.lean#L133-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ConnectionRaisingConstantEq.lean#L133-L136

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

theorem Formalism.FourierDecayAlt.P.NFx2.isPF_eq {f g : ℂ → A} (hf : IsPF f) (hg : IsPF g) {S : Set ℂ} (hS : S.Infinite)
    (h0 : ∀ Y ∈ S, f Y = g Y) : ∀ Y, f Y = g Y := by sorry
