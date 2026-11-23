-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Fr5_gauss_entries
-- name    : Formalism.FourierDecayAlt.P.Fr5.gauss_entries
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:58:24.597228+00:00
-- url     : https://prove2.me/theorems/de2924a4-4414-41c9-97be-7309a62815cc
-- title:
--   Fr5: gauss entries
-- statement:
--   The Fr5 construction uses the gauss entries property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FreeOf2OfFourEntries.lean#L154-L163
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FreeOf2OfFourEntries.lean#L154-L163

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
variable {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype S] [DecidableEq S]

theorem Formalism.FourierDecayAlt.P.Fr5.gauss_entries (Fs dd ls l p t F : SlopeTestRemainingChoices S A) :
    d0 Fs * !![1, ls; 0, 1] * d0 dd * !![p, 0; 0, t] * !![1, 0; l, 1] * d0 F =
      !![Fs * (dd * p + ls * (dd * t) * l) * F, Fs * (ls * (dd * t)) * F;
        Fs * (dd * t * l) * F, Fs * (dd * t) * F] := by sorry
