-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_sv_unitB_lie
-- name    : Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.sv_unitB_lie
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T16:47:17.786461+00:00
-- url     : https://prove2.me/theorems/084f7bca-94da-46a6-a129-054353b4cb8d
-- title:
--   Lie Algebra Weight Vectors: sv unit B lie
-- statement:
--   The Lie Algebra Weight Vectors construction uses the sv unit B lie property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuadraticFormTwoTwo/SmoothVec.lean#L276-L290
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuadraticFormTwoTwo/SmoothVec.lean#L276-L290

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_InLieW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_SmoothVec
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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}

theorem Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.sv_unitB_lie {z : Fin (2 * r + k + 1) → ℂ} {m : ℕ} {Bs : Fin m → Fin (2 * r + k + 1) → ℂ}
    (hBs : IsFrameOf k r [z] Bs) (a b : Fin m) :
    inLieW k r z (hpart1 (Hpk k r) (unitB (Hpk k r) Bs a b)) ∧
      inLieW k r z (hpart2 (Hpk k r) (unitB (Hpk k r) Bs a b)) := by sorry
