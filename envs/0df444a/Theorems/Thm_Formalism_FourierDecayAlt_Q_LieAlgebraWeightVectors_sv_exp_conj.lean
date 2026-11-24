-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_sv_exp_conj
-- name    : Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.sv_exp_conj
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T16:45:33.803394+00:00
-- url     : https://prove2.me/theorems/5a3d04e2-d405-43c1-9e38-b3cc1bba2b62
-- title:
--   Lie Algebra Weight Vectors: sv exp conj
-- statement:
--   The Lie Algebra Weight Vectors construction uses the sv exp conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuadraticFormTwoTwo/SmoothVec.lean#L120-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuadraticFormTwoTwo/SmoothVec.lean#L120-L129

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

theorem Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.sv_exp_conj {z : Fin (2 * r + k + 1) → ℂ} {X h h₀ : Mx k r} (hh₀ : h₀ ∈ UWset k r z) (t : ℝ) :
    h * NormedSpace.exp ((t : ℂ) • X) * h₀ = h * h₀ * NormedSpace.exp ((t : ℂ) • (h₀⁻¹ * X * h₀)) := by sorry
