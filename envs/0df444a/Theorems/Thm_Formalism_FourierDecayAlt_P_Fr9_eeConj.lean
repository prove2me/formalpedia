-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Fr9_eeConj
-- name    : Formalism.FourierDecayAlt.P.Fr9.eeConj
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T13:04:25.936887+00:00
-- url     : https://prove2.me/theorems/2205a573-daa5-406a-8060-760c6938c8e5
-- title:
--   Fr9: ee Conj
-- statement:
--   The Fr9 construction uses the ee Conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CommuteLevelZeroElement.lean#L447-L462
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CommuteLevelZeroElement.lean#L447-L462

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
variable {L : LevelData A r} {f : FrameData S A}

theorem Formalism.FourierDecayAlt.P.Fr9.eeConj (h : IsFrame L f) {Y Ya : ℂ} (hY : Y ∈ f.inv) (hY1 : Y + 1 ∈ f.inv) (ha : Ya ∈ f.inv)
    (ha1 : Ya + 1 ∈ f.inv) (hne : Y ≠ Ya) : f.xi Ya * f.ee Y * f.x Ya - f.DD Y Ya = f.ee Y := by sorry
