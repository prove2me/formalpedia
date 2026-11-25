-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_sb_diag
-- name    : Formalism.FourierDecayAlt.P.NFx2.sb_diag
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T16:18:38.450743+00:00
-- url     : https://prove2.me/theorems/1ca1501d-6dec-4616-b8eb-ff164e704b0f
-- title:
--   NFx2: sb diag
-- statement:
--   The NFx2 construction uses the sb diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ConnectionRaisingConstantEq.lean#L517-L528
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ConnectionRaisingConstantEq.lean#L517-L528

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

theorem Formalism.FourierDecayAlt.P.NFx2.sb_diag (h : SHyp P L0 QQ κ) (ρ : M.Ty P) {u v : ℂ} (hu : M.xC P ρ u ≠ 0) (hv : M.xC P ρ v ≠ 0) :
    (M.xC P ρ u)⁻¹ • lowerBlockAlt κ QQ ρ ρ u + u • (L0.ζb * proj κ ρ) =
      (M.xC P ρ v)⁻¹ • lowerBlockAlt κ QQ ρ ρ v + v • (L0.ζb * proj κ ρ) := by sorry
