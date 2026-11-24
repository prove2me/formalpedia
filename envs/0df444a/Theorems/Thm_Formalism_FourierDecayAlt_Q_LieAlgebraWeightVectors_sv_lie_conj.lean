-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_sv_lie_conj
-- name    : Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.sv_lie_conj
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T16:45:47.572114+00:00
-- url     : https://prove2.me/theorems/e9694787-5176-4b0b-a314-62a4072db6cf
-- title:
--   Lie Algebra Weight Vectors: sv lie conj
-- statement:
--   The Lie Algebra Weight Vectors construction uses the sv lie conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuadraticFormTwoTwo/SmoothVec.lean#L97-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuadraticFormTwoTwo/SmoothVec.lean#L97-L118

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

theorem Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.sv_lie_conj {z : Fin (2 * r + k + 1) → ℂ} {X h₀ : Mx k r} (hX : inLieW k r z X)
    (hh₀ : h₀ ∈ UWset k r z) : inLieW k r z (h₀⁻¹ * X * h₀) := by sorry
