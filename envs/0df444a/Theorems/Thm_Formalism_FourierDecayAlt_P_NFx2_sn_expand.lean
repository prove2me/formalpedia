-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_sn_expand
-- name    : Formalism.FourierDecayAlt.P.NFx2.sn_expand
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T16:18:28.18445+00:00
-- url     : https://prove2.me/theorems/8afc3ea8-2873-44cc-b22e-7c0e8e33b6b9
-- title:
--   NFx2: sn expand
-- statement:
--   The NFx2 construction uses the sn expand property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ConnectionRaisingConstantEq.lean#L976-L996
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ConnectionRaisingConstantEq.lean#L976-L996

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

theorem Formalism.FourierDecayAlt.P.NFx2.sn_expand {G Gi x xi m l S12 weightedSumBis : A} (hGG : Gi * G = 1) (hx : x * xi = 1) (hxi : xi * x = 1)
    (hmx : m * x = x * m) (hxGi : x * Gi = Gi * x) (hxiG : xi * G = G * xi) :
    (G * x * m + S12) * (Gi * xi) * (G * x * l + weightedSumBis) =
      G * x * m * l + G * m * Gi * weightedSumBis + S12 * l + S12 * (Gi * xi) * weightedSumBis := by sorry
