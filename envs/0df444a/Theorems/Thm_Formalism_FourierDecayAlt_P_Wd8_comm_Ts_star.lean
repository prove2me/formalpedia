-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Wd8_comm_Ts_star
-- name    : Formalism.FourierDecayAlt.P.Wd8.comm_Ts_star
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:17:44.33014+00:00
-- url     : https://prove2.me/theorems/c8b3afde-408c-4f93-b32b-995245ea9614
-- title:
--   Wd8: comm Ts star
-- statement:
--   The Wd8 construction uses the comm Ts star property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LiftMatrixTransferConjTransposeCommute.lean#L202-L213
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LiftMatrixTransferConjTransposeCommute.lean#L202-L213

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

theorem Formalism.FourierDecayAlt.P.Wd8.comm_Ts_star {R : Type} [Ring R] (φ : A →+* R)
    (hφ : ∀ (k : K) (r : R), Commute (φ (algebraMap K A k)) r)
    (τ : Site A) (b : R) (h : ∀ x ∈ ops τ, Commute (φ x) b) (Y : K) (i j : Fin 2) :
    Commute (φ (star (Ts τ Y i j))) b := by sorry
