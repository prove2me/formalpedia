-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Wd7_comm_Tstar
-- name    : Formalism.FourierDecayAlt.P.Wd7.comm_Tstar
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:48:22.123795+00:00
-- url     : https://prove2.me/theorems/730fb9df-d16b-4341-b8a8-0709febd5f25
-- title:
--   Wd7: comm Tstar
-- statement:
--   The Wd7 construction uses the comm Tstar property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ScalarCommuteTransposedRMatrixEntry.lean#L460-L472
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ScalarCommuteTransposedRMatrixEntry.lean#L460-L472

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

theorem Formalism.FourierDecayAlt.P.Wd7.comm_Tstar (σ : Site A) (Y : K) (z : A) (hz : ∀ x ∈ hol σ, Commute z (star x)) (i j : Fin 2) :
    Commute z (star (Ts σ Y i j)) := by sorry
