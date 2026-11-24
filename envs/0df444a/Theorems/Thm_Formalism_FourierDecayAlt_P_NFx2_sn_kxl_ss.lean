-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_sn_kxl_ss
-- name    : Formalism.FourierDecayAlt.P.NFx2.sn_kxl_ss
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T16:19:03.721797+00:00
-- url     : https://prove2.me/theorems/591dcc85-7895-4ceb-b4db-c053a9b0bbd2
-- title:
--   NFx2: sn kxl ss
-- statement:
--   The NFx2 construction uses the sn kxl ss property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ConnectionRaisingConstantEq.lean#L954-L956
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ConnectionRaisingConstantEq.lean#L954-L956

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

theorem Formalism.FourierDecayAlt.P.NFx2.sn_kxl_ss (hR : Raises κ SS) (j l : ℕ) (Y : ℂ) :
    κ (fun ρ => M.xEx P {l} ρ Y) * SS j = SS j * κ (fun ρ => sn_hsh P l j ρ Y) := by sorry
