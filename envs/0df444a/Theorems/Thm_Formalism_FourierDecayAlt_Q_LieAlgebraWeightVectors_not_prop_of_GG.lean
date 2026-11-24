-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_not_prop_of_GG
-- name    : Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.not_prop_of_GG
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T16:45:54.708989+00:00
-- url     : https://prove2.me/theorems/c8f72581-d229-4c26-a1a2-6853b7647c07
-- title:
--   Lie Algebra Weight Vectors: not prop of GG
-- statement:
--   The Lie Algebra Weight Vectors construction uses the not prop of GG property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuadraticFormTwoTwo/GANormSqStar.lean#L190-L227
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuadraticFormTwoTwo/GANormSqStar.lean#L190-L227

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_InLieW
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_GANormSqStar
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

theorem Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.not_prop_of_GG {z z' : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hz' : inWb k r z') {g : Mx k r}
    (hg : g ∈ Glev k r (Fin.last r)) (hGG : GGl k r z z' g ≠ 0) :
    (∀ c : ℂ, g⁻¹ *ᵥ z ≠ c • z') ∧ ∀ c : ℂ, g *ᵥ z' ≠ c • z := by sorry
