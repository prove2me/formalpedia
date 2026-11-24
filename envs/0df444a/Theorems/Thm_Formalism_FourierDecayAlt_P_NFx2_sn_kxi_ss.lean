-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_sn_kxi_ss
-- name    : Formalism.FourierDecayAlt.P.NFx2.sn_kxi_ss
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T16:19:11.345448+00:00
-- url     : https://prove2.me/theorems/c0ef29b4-9e06-4f64-b60f-3f544ead4255
-- title:
--   NFx2: sn kxi ss
-- statement:
--   The NFx2 construction uses the sn kxi ss property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ConnectionRaisingConstantEq.lean#L950-L952
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ConnectionRaisingConstantEq.lean#L950-L952

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
variable {P : M.Par} {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] {L : R.LevelData A P.r}
  {κ : (M.Ty P → ℂ) →ₐ[ℂ] A} {SS : ℕ → A}

theorem Formalism.FourierDecayAlt.P.NFx2.sn_kxi_ss (hR : Raises κ SS) {j : ℕ} (hj : j ∈ Icc 1 (P.k - 1)) (Y : ℂ) :
    xiA κ Y * SS j = SS j * κ (fun ρ => ((Y + M.rho P ρ j + 1) * M.xEx P {j} ρ Y)⁻¹) := by sorry
