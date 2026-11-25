-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_LeftDerivativeCurves_uh_mul_inv
-- name    : Formalism.FourierDecayAlt.P.LeftDerivativeCurves.uh_mul_inv
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:12:49.77886+00:00
-- url     : https://prove2.me/theorems/cc476c1c-e3b8-4b58-aecb-a95300d116c5
-- title:
--   Left Derivative Curves: uh mul inv
-- statement:
--   The Left Derivative Curves construction uses the uh mul inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LeftDerivativeCurves.lean#L265-L269
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LeftDerivativeCurves.lean#L265-L269

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
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {i : Fin (r + 1)}

theorem Formalism.FourierDecayAlt.P.LeftDerivativeCurves.uh_mul_inv {g : Mx k r} (hg : g ∈ UH (Hpk k r)) : g * g⁻¹ = 1 := by sorry
