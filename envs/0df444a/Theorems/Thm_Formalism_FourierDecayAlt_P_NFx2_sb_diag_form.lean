-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_sb_diag_form
-- name    : Formalism.FourierDecayAlt.P.NFx2.sb_diag_form
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T16:18:47.22734+00:00
-- url     : https://prove2.me/theorems/a654c8e0-c864-4db0-ab1d-7e015346197d
-- title:
--   NFx2: sb diag form
-- statement:
--   The NFx2 construction uses the sb diag form property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ConnectionRaisingConstantEq.lean#L734-L742
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ConnectionRaisingConstantEq.lean#L734-L742

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

theorem Formalism.FourierDecayAlt.P.NFx2.sb_diag_form (h : SHyp P L0 QQ κ) (ρ : M.Ty P) {Y : ℂ} (hY : Reg P Y) :
    (sb_b L0 κ QQ ρ - Y • (L0.ζb * L0.GGi)) * proj κ ρ = (M.xC P ρ Y)⁻¹ • (L0.GGi * lowerBlockAlt κ QQ ρ ρ Y) := by sorry
