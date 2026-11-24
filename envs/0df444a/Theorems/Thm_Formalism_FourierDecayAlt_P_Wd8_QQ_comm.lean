-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Wd8_QQ_comm
-- name    : Formalism.FourierDecayAlt.P.Wd8.QQ_comm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:47:02.559846+00:00
-- url     : https://prove2.me/theorems/ad6cda7d-e15e-4d63-90ee-24faca57b954
-- title:
--   Wd8: QQ comm
-- statement:
--   The Wd8 construction uses the QQ comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LiftMatrixTransferConjTransposeCommute.lean#L365-L370
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LiftMatrixTransferConjTransposeCommute.lean#L365-L370

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

theorem Formalism.FourierDecayAlt.P.Wd8.QQ_comm (QQ : K → M2 A) (sites : List (Site A)) (w : List (Letter K S)) (Y : K)
    (h : ∀ σ ∈ sites, QQCommutes QQ σ) :
    Commute (lift0 (QQ Y)) (d0 (sites.map fun σ => bT σ w).prod) := by sorry
