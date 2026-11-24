-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Wd8_comm_Ts
-- name    : Formalism.FourierDecayAlt.P.Wd8.comm_Ts
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:17:30.050523+00:00
-- url     : https://prove2.me/theorems/f5cc1bc3-933e-46a3-a7b1-b29c798dc515
-- title:
--   Wd8: comm Ts
-- statement:
--   The Wd8 construction uses the comm Ts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LiftMatrixTransferConjTransposeCommute.lean#L193-L200
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LiftMatrixTransferConjTransposeCommute.lean#L193-L200

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

theorem Formalism.FourierDecayAlt.P.Wd8.comm_Ts {R : Type} [Ring R] (φ : A →+* R) (hφ : ∀ (k : K) (r : R), Commute (φ (algebraMap K A k)) r)
    (τ : Site A) (b : R) (h : ∀ x ∈ ops τ, Commute (φ x) b) (Y : K) (i j : Fin 2) :
    Commute (φ (Ts τ Y i j)) b := by sorry
