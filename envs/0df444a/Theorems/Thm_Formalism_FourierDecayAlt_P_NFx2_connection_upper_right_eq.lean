-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_connection_upper_right_eq
-- name    : Formalism.FourierDecayAlt.P.NFx2.connection_upper_right_eq
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T15:15:35.56583+00:00
-- url     : https://prove2.me/theorems/20c86f96-0f81-40d4-b86d-96c6c7ac08cf
-- title:
--   NFx2: connection upper right eq
-- statement:
--   The NFx2 construction uses the connection upper right eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ConnectionRaisingConstantEq.lean#L2078-L2086
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ConnectionRaisingConstantEq.lean#L2078-L2086

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

theorem Formalism.FourierDecayAlt.P.NFx2.connection_upper_right_eq (h : SHyp P L0 QQ κ) (hF : SForm P L0 QQ κ b SS) (hR : Raises κ SS) (Y : ℂ) :
    QQ Y 0 1 = (Q.NFData.QQ (⟨sc_LL h hF, κ, SS⟩ : Q.NFData P A) Y) 0 1 := by sorry
