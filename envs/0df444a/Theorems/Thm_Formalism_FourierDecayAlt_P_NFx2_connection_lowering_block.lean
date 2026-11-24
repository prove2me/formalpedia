-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_connection_lowering_block
-- name    : Formalism.FourierDecayAlt.P.NFx2.connection_lowering_block
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T16:17:25.360956+00:00
-- url     : https://prove2.me/theorems/1f7005bf-f370-48b4-83db-da93de16977f
-- title:
--   NFx2: connection lowering block
-- statement:
--   The NFx2 construction uses the connection lowering block property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ConnectionRaisingConstantEq.lean#L1950-L1955
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ConnectionRaisingConstantEq.lean#L1950-L1955

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

theorem Formalism.FourierDecayAlt.P.NFx2.connection_lowering_block (h : SHyp P L0 QQ κ) (hF : SForm P L0 QQ κ b SS) (Y : ℂ) (σ τ : M.Ty P) :
    proj κ σ * (sc_LL h hF).l0 Y * proj κ τ = if σ = τ then (b σ - Y • (L0.ζb * L0.GGi)) * proj κ σ else 0 := by sorry
