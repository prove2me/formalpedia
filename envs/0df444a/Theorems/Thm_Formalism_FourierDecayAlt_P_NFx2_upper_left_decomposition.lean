-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_upper_left_decomposition
-- name    : Formalism.FourierDecayAlt.P.NFx2.upper_left_decomposition
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T15:21:21.912868+00:00
-- url     : https://prove2.me/theorems/21f1e4ec-df77-4088-9425-2bd66217b0ed
-- title:
--   NFx2: upper left decomposition
-- statement:
--   The NFx2 construction uses the upper left decomposition property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ConnectionRaisingConstantEq.lean#L1168-L1172
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ConnectionRaisingConstantEq.lean#L1168-L1172

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

theorem Formalism.FourierDecayAlt.P.NFx2.upper_left_decomposition (Y : ℂ) : (Q.NFData.QQ (⟨L, κ, SS⟩ : Q.NFData P A) Y) 0 0 =
    L.GGi * κ (fun ρ => M.wC P ρ Y) + upperLeftTail L κ SS Y + L.GGi * Q.NFData.S4 (⟨L, κ, SS⟩ : Q.NFData P A) Y := by sorry
