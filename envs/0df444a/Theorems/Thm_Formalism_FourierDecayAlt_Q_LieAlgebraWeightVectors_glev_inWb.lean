-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_glev_inWb
-- name    : Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.glev_inWb
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T15:47:36.795706+00:00
-- url     : https://prove2.me/theorems/a257b219-097d-484a-8092-0685ebdcf10f
-- title:
--   Lie Algebra Weight Vectors: glev in Wb
-- statement:
--   The Lie Algebra Weight Vectors construction uses the glev in Wb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuadraticFormTwoTwo/GANormSqStar.lean#L160-L185
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuadraticFormTwoTwo/GANormSqStar.lean#L160-L185

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

theorem Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.glev_inWb {g : Mx k r} (hg : g ∈ Glev k r (Fin.last r)) {v : Fin (2 * r + k + 1) → ℂ}
    (hv : inWb k r v) : inWb k r (g *ᵥ v) ∧ inWb k r (g⁻¹ *ᵥ v) := by sorry
