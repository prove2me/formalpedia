-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Wd7_Rh0_col
-- name    : Formalism.FourierDecayAlt.P.Wd7.Rh0_col
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T21:46:10.64418+00:00
-- url     : https://prove2.me/theorems/be4dbf1b-4d86-479d-a440-23d006ddf9bd
-- title:
--   Wd7: Rh0 col
-- statement:
--   The Wd7 construction uses the Rh0 col property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ScalarCommuteTransposedRMatrixEntry.lean#L281-L296
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ScalarCommuteTransposedRMatrixEntry.lean#L281-L296

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

theorem Formalism.FourierDecayAlt.P.Wd7.Rh0_col (a : S) (D : K) (hD : D ≠ 1) (m : Fin 2) (z : Ix S) :
    (Rh0 a D m 0 : SlopeTestRemainingChoices S A) z e1 = if m = 0 ∧ z = e1 then 1 else 0 := by sorry
