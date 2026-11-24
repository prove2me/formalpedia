-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_sn_e_other
-- name    : Formalism.FourierDecayAlt.P.NFx2.sn_e_other
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T16:19:59.903842+00:00
-- url     : https://prove2.me/theorems/d0a74576-8be3-42f3-8199-885dba6aaebf
-- title:
--   NFx2: sn e other
-- statement:
--   The NFx2 construction uses the sn e other property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ConnectionRaisingConstantEq.lean#L1289-L1295
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ConnectionRaisingConstantEq.lean#L1289-L1295

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

theorem Formalism.FourierDecayAlt.P.NFx2.sn_e_other {j l : ℕ} (hl : l ∈ Icc 1 (P.k - 1)) (hjl : j ≠ l) (τ : M.Ty P) :
    sn_e P τ j ((-(M.rho P τ l) - 1 : ℝ) : ℂ) = 0 := by sorry
