-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_sn_kxl_sss
-- name    : Formalism.FourierDecayAlt.P.NFx2.sn_kxl_sss
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T16:18:52.157729+00:00
-- url     : https://prove2.me/theorems/ed8ae85e-cc3b-473c-a3f1-3ab90df419e2
-- title:
--   NFx2: sn kxl sss
-- statement:
--   The NFx2 construction uses the sn kxl sss property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ConnectionRaisingConstantEq.lean#L958-L965
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ConnectionRaisingConstantEq.lean#L958-L965

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

theorem Formalism.FourierDecayAlt.P.NFx2.sn_kxl_sss (hc : RelCore (⟨L, κ, SS⟩ : Q.NFData P A)) (l : ℕ) (Y : ℂ) :
    κ (fun ρ => M.xEx P {l} ρ Y) * star (SS l) = star (SS l) * κ (fun ρ => M.xEx P {l} ρ Y) := by sorry
