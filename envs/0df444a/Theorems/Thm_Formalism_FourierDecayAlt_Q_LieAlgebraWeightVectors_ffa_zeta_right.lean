-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_ffa_zeta_right
-- name    : Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.ffa_zeta_right
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T16:44:55.3488+00:00
-- url     : https://prove2.me/theorems/ca59ea8f-a90c-43a4-a3de-1a43c32cfe86
-- title:
--   Lie Algebra Weight Vectors: ffa zeta right
-- statement:
--   The Lie Algebra Weight Vectors construction uses the ffa zeta right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuadraticFormTwoTwo/TopLevelPointwiseIdentity.lean#L94-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuadraticFormTwoTwo/TopLevelPointwiseIdentity.lean#L94-L98

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_GANormSqStar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_TopLevelPointwiseIdentity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}

theorem Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.ffa_zeta_right {z z' : Fin (2 * r + k + 1) → ℂ} {h' : Mx k r} (hz' : h' *ᵥ z' = z')
    (g : Mx k r) : zetaL k r z z' (Fin.last r) (g * h') = zetaL k r z z' (Fin.last r) g := by sorry
