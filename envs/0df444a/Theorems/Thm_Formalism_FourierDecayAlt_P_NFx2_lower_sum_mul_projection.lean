-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_lower_sum_mul_projection
-- name    : Formalism.FourierDecayAlt.P.NFx2.lower_sum_mul_projection
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T16:18:00.689005+00:00
-- url     : https://prove2.me/theorems/f6244c8b-9e51-4274-a9a9-dad720c3f5f0
-- title:
--   NFx2: lower sum mul projection
-- statement:
--   The NFx2 construction uses the lower sum mul projection property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ConnectionRaisingConstantEq.lean#L1016-L1023
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ConnectionRaisingConstantEq.lean#L1016-L1023

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

theorem Formalism.FourierDecayAlt.P.NFx2.lower_sum_mul_projection (τ : M.Ty P) (Y : ℂ) :
    Q.NFData.weightedSumBis (⟨L, κ, SS⟩ : Q.NFData P A) Y * proj κ τ =
      ∑ j ∈ Icc 1 (P.k - 1), M.xEx P {j} τ Y • (SS j * proj κ τ) := by sorry
