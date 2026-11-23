-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Wd8_io_comm_bT
-- name    : Formalism.FourierDecayAlt.P.Wd8.io_comm_bT
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T02:34:21.584961+00:00
-- url     : https://prove2.me/theorems/97dcf9b4-a4b0-4275-9c7b-e49d6cb41853
-- title:
--   Wd8: io comm b T
-- statement:
--   The Wd8 construction uses the io comm b T property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LiftMatrixTransferConjTransposeCommute.lean#L235-L243
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LiftMatrixTransferConjTransposeCommute.lean#L235-L243

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

theorem Formalism.FourierDecayAlt.P.Wd8.io_comm_bT (σ : Site A) (x : A) (h : ∀ y ∈ ops σ, Commute y x) (w : List (Letter K S)) :
    Commute (io x) (bT σ w : SlopeTestRemainingChoices S A) := by sorry
