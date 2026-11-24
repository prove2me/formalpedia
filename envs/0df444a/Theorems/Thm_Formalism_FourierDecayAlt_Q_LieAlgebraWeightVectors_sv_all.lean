-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_sv_all
-- name    : Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.sv_all
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T16:46:05.802457+00:00
-- url     : https://prove2.me/theorems/c5eb495a-259c-4d29-8810-7386714e1ab7
-- title:
--   Lie Algebra Weight Vectors: sv all
-- statement:
--   The Lie Algebra Weight Vectors construction uses the sv all property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuadraticFormTwoTwo/SmoothVec.lean#L164-L171
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuadraticFormTwoTwo/SmoothVec.lean#L164-L171

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
variable {Wp : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ}
  {π : Mx k r → (Wp →L[ℂ] Wp)}

theorem Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.sv_all {u : ℕ → ℝ} (hπ : IsType k r z π u) {x₀ : Wp} (hx₀ : x₀ ≠ 0) (hsm : x₀ ∈ SmVec k r z π)
    (v : Wp) : v ∈ SmVec k r z π := by sorry
