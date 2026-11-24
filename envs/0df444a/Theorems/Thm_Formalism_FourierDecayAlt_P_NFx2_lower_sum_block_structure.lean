-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_lower_sum_block_structure
-- name    : Formalism.FourierDecayAlt.P.NFx2.lower_sum_block_structure
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T15:28:34.020524+00:00
-- url     : https://prove2.me/theorems/2d51b477-6dbb-43be-a7b2-f1b806498f1c
-- title:
--   NFx2: lower sum block structure
-- statement:
--   The NFx2 construction uses the lower sum block structure property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ConnectionRaisingConstantEq.lean#L2113-L2118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ConnectionRaisingConstantEq.lean#L2113-L2118

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

theorem Formalism.FourierDecayAlt.P.NFx2.lower_sum_block_structure (hR : Raises κ SS) (Y : ℂ) :
    GlobalTheory κ (fun τ σ => ∃ j ∈ Icc 1 (P.k - 1), M.Up P j τ σ)
      (∑ l ∈ Icc 1 (P.k - 1), SS l * κ (fun ρ => M.xEx P {l} ρ Y)) := by sorry
