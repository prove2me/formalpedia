-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Wd8_liftMatrix_transfer_conjTranspose_commute
-- name    : Formalism.FourierDecayAlt.P.Wd8.liftMatrix_transfer_conjTranspose_commute
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:47:15.031843+00:00
-- url     : https://prove2.me/theorems/3e4f81ba-a731-49c0-8950-0eb429401cea
-- title:
--   Wd8: lift Matrix transfer conj Transpose commute
-- statement:
--   The Wd8 construction uses the lift Matrix transfer conj Transpose commute property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LiftMatrixTransferConjTransposeCommute.lean#L261-L267
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LiftMatrixTransferConjTransposeCommute.lean#L261-L267

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EntryCommuteTransposedRMatrix
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ScalarCommuteTransposedRMatrixEntry
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LiftMatrixTransferConjTransposeCommute
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd8
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd
variable {K A S : Type} [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
  [Fintype S] [DecidableEq S]

theorem Formalism.FourierDecayAlt.P.Wd8.liftMatrix_transfer_conjTranspose_commute {τ : Site A} {b : SlopeTestRemainingChoices S A} (h : CC τ b) (Y : K) :
    Commute (lift0 (Ts τ Y)ᴴ) (d0 b) := by sorry
