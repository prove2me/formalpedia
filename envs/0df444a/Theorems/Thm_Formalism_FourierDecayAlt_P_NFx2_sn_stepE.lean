-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_sn_stepE
-- name    : Formalism.FourierDecayAlt.P.NFx2.sn_stepE
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T16:19:20.002029+00:00
-- url     : https://prove2.me/theorems/22f0459f-2bf2-43ca-ab19-cdac53f10923
-- title:
--   NFx2: sn step E
-- statement:
--   The NFx2 construction uses the sn step E property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ConnectionRaisingConstantEq.lean#L1051-L1071
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ConnectionRaisingConstantEq.lean#L1051-L1071

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

theorem Formalism.FourierDecayAlt.P.NFx2.sn_stepE (hc : RelCore (⟨L, κ, SS⟩ : Q.NFData P A)) {Y : ℂ} (hY : Reg P Y) {j : ℕ}
    (hj : j ∈ Icc 1 (P.k - 1)) (τ : M.Ty P) :
    ∑ l ∈ Icc 1 (P.k - 1), (M.xEx P {j} τ Y * ((Y + M.rho P τ j + 1) * M.xEx P {j} τ Y)⁻¹ * sn_hsh P l j τ Y) •
        (star (SS l) * SS j * proj κ τ) =
      (M.xEx P {j} τ Y / (Y + M.rho P τ j + 1)) • (star (SS j) * SS j * proj κ τ) +
        ∑ l ∈ (Icc 1 (P.k - 1)).erase j, M.xEx P {l, j} τ Y • (star (SS l) * SS j * proj κ τ) := by sorry
