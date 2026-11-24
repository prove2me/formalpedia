-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_connection_lower_left_entry
-- name    : Formalism.FourierDecayAlt.P.NFx2.connection_lower_left_entry
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T15:09:58.746264+00:00
-- url     : https://prove2.me/theorems/04af23c2-fe28-497a-8b10-c89175681d3e
-- title:
--   NFx2: connection lower left entry
-- statement:
--   The NFx2 construction uses the connection lower left entry property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ConnectionRaisingConstantEq.lean#L1964-L1966
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ConnectionRaisingConstantEq.lean#L1964-L1966

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

theorem Formalism.FourierDecayAlt.P.NFx2.connection_lower_left_entry (h : SHyp P L0 QQ κ) (hF : SForm P L0 QQ κ b SS) (Y : ℂ) :
    (Q.NFData.QQ (⟨sc_LL h hF, κ, SS⟩ : Q.NFData P A) Y) 1 0 =
      L0.GG * xA κ Y * (sc_LL h hF).l0 Y + ∑ l ∈ Icc 1 (P.k - 1), SS l * κ (fun ρ => M.xEx P {l} ρ Y) := by sorry
