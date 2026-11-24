-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_upper_left_tail_projection
-- name    : Formalism.FourierDecayAlt.P.NFx2.upper_left_tail_projection
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T16:39:05.063802+00:00
-- url     : https://prove2.me/theorems/f5cf5cd6-b6ea-4a9d-9c99-eb396507c090
-- title:
--   NFx2: upper left tail projection
-- statement:
--   The NFx2 construction uses the upper left tail projection property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ConnectionRaisingConstantEq.lean#L1073-L1099
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ConnectionRaisingConstantEq.lean#L1073-L1099

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

theorem Formalism.FourierDecayAlt.P.NFx2.upper_left_tail_projection (hc : RelCore (⟨L, κ, SS⟩ : Q.NFData P A)) (hs : Fr.IsStarLevel L) {Y : ℂ} (hY : Reg P Y)
    (τ : M.Ty P) :
    Q.NFData.S12 (⟨L, κ, SS⟩ : Q.NFData P A) Y * (L.GGi * xiA κ Y) * Q.NFData.weightedSumBis (⟨L, κ, SS⟩ : Q.NFData P A) Y *
        proj κ τ =
      L.GGi * (∑ j ∈ Icc 1 (P.k - 1), (M.xEx P {j} τ Y / (Y + M.rho P τ j + 1)) • (star (SS j) * SS j * proj κ τ)) +
        L.GGi * (Q.NFData.S4 (⟨L, κ, SS⟩ : Q.NFData P A) Y * proj κ τ) := by sorry
