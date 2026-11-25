-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Wd7_Rht0_row
-- name    : Formalism.FourierDecayAlt.P.Wd7.Rht0_row
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:46:12.952229+00:00
-- url     : https://prove2.me/theorems/cdc33b1c-fd46-43bb-94bb-1eb067429ca9
-- title:
--   Wd7: Rht0 row
-- statement:
--   The Wd7 construction uses the Rht0 row property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ScalarCommuteTransposedRMatrixEntry.lean#L326-L344
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ScalarCommuteTransposedRMatrixEntry.lean#L326-L344

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EntryCommuteTransposedRMatrix
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ScalarCommuteTransposedRMatrixEntry
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd7
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd
variable {K A S : Type} [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
  [Fintype S] [DecidableEq S]

theorem Formalism.FourierDecayAlt.P.Wd7.Rht0_row (b : S) (d : K) (hd : d ≠ 1) (X : M2 (SlopeTestRemainingChoices S A)) (hX : FreeOf2 b X)
    (k : Fin 2) (z : Ix S) : ((Rht0 b d * X : M2 (SlopeTestRemainingChoices S A)) 0 k) z e1 = (X 0 k) z e1 := by sorry
