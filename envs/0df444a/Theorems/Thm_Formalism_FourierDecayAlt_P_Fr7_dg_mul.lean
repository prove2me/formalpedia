-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Fr7_dg_mul
-- name    : Formalism.FourierDecayAlt.P.Fr7.dg_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:39:12.090855+00:00
-- url     : https://prove2.me/theorems/44f5ee88-8055-43b3-a5ad-22e39115cd4c
-- title:
--   Fr7: dg mul
-- statement:
--   The Fr7 construction uses the dg mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PlusLetterFrameOfData.lean#L149-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PlusLetterFrameOfData.lean#L149-L154

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PlusLetterFrameOfData
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Fr7
open Formalism.FourierDecayAlt.P.Wd1
variable {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [Fintype S] [DecidableEq S] {a : S}

theorem Formalism.FourierDecayAlt.P.Fr7.dg_mul {p q p' q' : SlopeTestRemainingChoices S A} (hp : FreeOf a p) (hq : FreeOf a q) :
    ins a !![p, 0; 0, q] * ins a !![p', 0; 0, q'] = ins a !![p * p', 0; 0, q * q'] := by sorry
