-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_sn_core
-- name    : Formalism.FourierDecayAlt.P.NFx2.sn_core
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T15:21:31.422351+00:00
-- url     : https://prove2.me/theorems/462aca71-7b4d-4c3b-9d6f-ebfec8dbf7cc
-- title:
--   NFx2: sn core
-- statement:
--   The NFx2 construction uses the sn core property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ConnectionRaisingConstantEq.lean#L1185-L1222
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ConnectionRaisingConstantEq.lean#L1185-L1222

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

theorem Formalism.FourierDecayAlt.P.NFx2.sn_core (hc : RelCore (⟨L, κ, SS⟩ : Q.NFData P A)) (hs : Fr.IsStarLevel L) {QQ : ℂ → Matrix (Fin 2) (Fin 2) A}
    (h22 : ∀ Y, QQ Y 1 1 = L.GG * xA κ Y)
    (h21 : ∀ Y, QQ Y 1 0 = L.GG * xA κ Y * L.l0 Y + Q.NFData.weightedSumBis (⟨L, κ, SS⟩ : Q.NFData P A) Y)
    (h12 : ∀ Y, QQ Y 0 1 = L.GG * xA κ Y * L.m0 Y + Q.NFData.S12 (⟨L, κ, SS⟩ : Q.NFData P A) Y)
    (hD3 : ∀ Y, QQ Y 0 0 * QQ (Y + 1) 1 1 - QQ Y 0 1 * QQ (Y + 1) 1 0 = algebraMap ℂ A (M.qC P Y))
    (hD4 : ∀ Y, QQ Y 1 0 * QQ (Y + 1) 1 1 = QQ Y 1 1 * QQ (Y + 1) 1 0)
    {Y : ℂ} (hY : Reg P Y) (hY1 : Reg P (Y + 1)) (τ : M.Ty P) :
    QQ Y 0 0 * proj κ τ = (M.qC P Y / M.xC P τ (Y + 1)) • (L.GGi * proj κ τ) + upperLeftTail L κ SS Y * proj κ τ +
      (L.GGi * (∑ j ∈ Icc 1 (P.k - 1), (M.xEx P {j} τ Y / (Y + M.rho P τ j + 1)) • (star (SS j) * SS j * proj κ τ)) +
        L.GGi * (Q.NFData.S4 (⟨L, κ, SS⟩ : Q.NFData P A) Y * proj κ τ)) := by sorry
