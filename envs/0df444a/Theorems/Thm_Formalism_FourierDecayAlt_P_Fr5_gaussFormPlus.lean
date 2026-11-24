-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Fr5_gaussFormPlus
-- name    : Formalism.FourierDecayAlt.P.Fr5.gaussFormPlus
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:38:38.261492+00:00
-- url     : https://prove2.me/theorems/7b76532e-897c-4477-9b02-05b09f3d999d
-- title:
--   Fr5: gauss Form Plus
-- statement:
--   The Fr5 construction uses the gauss Form Plus property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FreeOf2OfFourEntries.lean#L275-L358
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FreeOf2OfFourEntries.lean#L275-L358

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QEFirstMulSecondEqSwap
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FreeOf2OfFourEntries
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Fr5
variable {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype S] [DecidableEq S] {r : ℕ}

theorem Formalism.FourierDecayAlt.P.Fr5.gaussFormPlus (L : LevelData A r) (f : FrameData S A) (a : S) (Ya : ℂ) (H : PlusHyp L f a Ya) :
    f.RR * ins a (f.TT Ya) = star (ins a !![1, 0; f.l L Ya, 1] * f.F) *
      (f.d L * ins a !![f.q Ya • (io L.GGi * f.xi (Ya + 1)), 0; 0, io L.GG * f.x Ya]) *
      (ins a !![1, 0; f.l L Ya, 1] * f.F) := by sorry
