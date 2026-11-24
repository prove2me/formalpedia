-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_sc_isPF_xEx
-- name    : Formalism.FourierDecayAlt.P.NFx2.sc_isPF_xEx
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T15:21:05.267878+00:00
-- url     : https://prove2.me/theorems/d7711d0b-504e-4cc9-8c99-7c7cd7e8912a
-- title:
--   NFx2: sc is PF x Ex
-- statement:
--   The NFx2 construction uses the sc is PF x Ex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ConnectionRaisingConstantEq.lean#L1904-L1905
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ConnectionRaisingConstantEq.lean#L1904-L1905

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
variable {P : M.Par} {A : Type} [Ring A] [StarRing A] [Algebra ℂ A]
variable {L0 : PreLevel A P.r} {QQ : ℂ → Matrix (Fin 2) (Fin 2) A} {κ : (M.Ty P → ℂ) →ₐ[ℂ] A}
  {b : M.Ty P → A} {SS : ℕ → A}

theorem Formalism.FourierDecayAlt.P.NFx2.sc_isPF_xEx (κ : (M.Ty P → ℂ) →ₐ[ℂ] A) (ex : Finset ℕ) : IsPF fun Y => κ (fun ρ => M.xEx P ex ρ Y) := by sorry
