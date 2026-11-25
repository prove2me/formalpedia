-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_LeftDerivativeCurves_lcurve_lev
-- name    : Formalism.FourierDecayAlt.P.LeftDerivativeCurves.lcurve_lev
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T04:30:38.9018+00:00
-- url     : https://prove2.me/theorems/16b23a02-0415-53a1-8698-3450c144386f
-- title:
--   Left Derivative Curves: lcurve lev
-- statement:
--   The Left Derivative Curves construction uses the lcurve lev property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LeftDerivativeCurves.lean#L39-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LeftDerivativeCurves.lean#L39-L58

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

theorem Formalism.FourierDecayAlt.P.LeftDerivativeCurves.lcurve_lev {g X : Mx k r} (hg : g ∈ Glev k r i) (hX : inLieLev k r i X) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • X) * g ∈ Glev k r i := by sorry
