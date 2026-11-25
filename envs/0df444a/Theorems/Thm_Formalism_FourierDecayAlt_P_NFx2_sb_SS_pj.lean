-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_sb_SS_pj
-- name    : Formalism.FourierDecayAlt.P.NFx2.sb_SS_pj
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T16:17:51.554688+00:00
-- url     : https://prove2.me/theorems/11a119ea-008a-4ddf-8f19-e7e1777b58d6
-- title:
--   NFx2: sb SS pj
-- statement:
--   The NFx2 construction uses the sb SS pj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ConnectionRaisingConstantEq.lean#L683-L698
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ConnectionRaisingConstantEq.lean#L683-L698

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
variable {P : M.Par} {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] {L0 : PreLevel A P.r}
  {QQ : ℂ → Matrix (Fin 2) (Fin 2) A} {κ : (M.Ty P → ℂ) →ₐ[ℂ] A}

theorem Formalism.FourierDecayAlt.P.NFx2.sb_SS_pj {l : ℕ} (hl : l ∈ Icc 1 (P.k - 1)) {ρ σ : M.Ty P} (hup : M.Up P l ρ σ) :
    sb_SS κ QQ l * proj κ ρ = sb_K κ QQ l ρ σ := by sorry
