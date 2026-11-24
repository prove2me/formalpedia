-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_lower_sum_square_raising_zero
-- name    : Formalism.FourierDecayAlt.P.NFx2.lower_sum_square_raising_zero
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T16:17:22.561706+00:00
-- url     : https://prove2.me/theorems/3202ad25-e19b-44bc-b943-0b581a921288
-- title:
--   NFx2: lower sum square raising zero
-- statement:
--   The NFx2 construction uses the lower sum square raising zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ConnectionRaisingConstantEq.lean#L2127-L2133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ConnectionRaisingConstantEq.lean#L2127-L2133

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

theorem Formalism.FourierDecayAlt.P.NFx2.lower_sum_square_raising_zero (hR : Raises κ SS) {l : ℕ} (hl : l ∈ Icc 1 (P.k - 1)) {ρ ρ' : M.Ty P} (hu : M.Up P l ρ ρ')
    (u v : ℂ) :
    proj κ ρ' * ((∑ l ∈ Icc 1 (P.k - 1), SS l * κ (fun ρ => M.xEx P {l} ρ u)) *
      (∑ l ∈ Icc 1 (P.k - 1), SS l * κ (fun ρ => M.xEx P {l} ρ v))) * proj κ ρ = 0 := by sorry
