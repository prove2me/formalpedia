-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Fr9_tau_mat
-- name    : Formalism.FourierDecayAlt.P.Fr9.tau_mat
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T13:19:28.619197+00:00
-- url     : https://prove2.me/theorems/69568a4f-24a7-4e8b-81a0-485022264573
-- title:
--   Fr9: tau mat
-- statement:
--   The Fr9 construction uses the tau mat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CommuteLevelZeroElement.lean#L244-L259
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CommuteLevelZeroElement.lean#L244-L259

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagScalarCommuteTransposedRMatrix
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRelationFirst
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CommuteLevelZeroElement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Fr9
variable {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype S] [DecidableEq S]
  {r : ℕ}

theorem Formalism.FourierDecayAlt.P.Fr9.tau_mat {B : Type*} [Ring B] [Algebra ℂ B] {zbi zg m τ t12 : B} {d : ℂ}
    (h1 : Commute zbi τ) (h2 : Commute zg τ) (hk : d • (m * τ - τ * m) = t12 - τ * m) :
    !![zbi, 0; zg * m, zg] * !![d • τ, 0; -t12, (d - 1) • τ] =
      !![d • τ, 0; 0, (d - 1) • τ] * !![zbi, 0; zg * m, zg] := by sorry
