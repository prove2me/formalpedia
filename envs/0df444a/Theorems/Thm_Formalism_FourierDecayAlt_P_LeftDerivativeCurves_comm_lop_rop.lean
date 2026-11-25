-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_LeftDerivativeCurves_comm_lop_rop
-- name    : Formalism.FourierDecayAlt.P.LeftDerivativeCurves.comm_lop_rop
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T05:11:56.694296+00:00
-- url     : https://prove2.me/theorems/8f54009c-aaea-5548-8ed0-b641d8b481aa
-- title:
--   Left Derivative Curves: comm lop rop
-- statement:
--   The Left Derivative Curves construction uses the comm lop rop property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LeftDerivativeCurves.lean#L245-L251
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LeftDerivativeCurves.lean#L245-L251

import Definitions.Def_Formalism_HermitianCurvature_StatementQr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RestrictionIrrelevantDoubleLevelOperator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LeftDerivativeCurves
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt.P.LeftDerivativeCurves
open Qx2 (Good)
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {i : Fin (r + 1)} {D : Set (Mx k r)}

theorem Formalism.FourierDecayAlt.P.LeftDerivativeCurves.comm_lop_rop (hD : IsOpen D) {Z Z' : Mx k r} (h1 : inLieLev k r i (hpart1 (Hpk k r) Z))
    (h2 : inLieLev k r i (hpart2 (Hpk k r) Z)) (h1' : inLieLev k r i (hpart1 (Hpk k r) Z'))
    (h2' : inLieLev k r i (hpart2 (Hpk k r) Z')) (c c' : ℂ) :
    Comm (E := E) k r i D (lop k r c Z) (rop k r c' Z') := by sorry
