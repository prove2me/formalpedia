-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_Q_LeftMultiplicationRule_rdV_left
-- name    : Formalism.FourierDecayAlt.Q.LeftMultiplicationRule.rdV_left
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T16:45:40.315103+00:00
-- url     : https://prove2.me/theorems/c8c31a83-6c24-4c54-9234-6a62e8ad9a77
-- title:
--   Left Multiplication Rule: rd V left
-- statement:
--   The Left Multiplication Rule construction uses the rd V left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LeftPhaseRule/HasDerivAtPhase.lean#L125-L179
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LeftPhaseRule/HasDerivAtPhase.lean#L125-L179

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_CapelliHighestWeightConjugated
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LeftPhaseRule_MulApplyS
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LeftPhaseRule_ReflectionColumnDualIsotropic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LeftPhaseRule_HasDerivAtPhase
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.QuantumDeterminants.WeylGroupFacts
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.LeftMultiplicationRule
variable {k r : ℕ}

theorem Formalism.FourierDecayAlt.Q.LeftMultiplicationRule.rdV_left {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {z : Fin (2 * r + k + 1) → ℂ}
    (hz : inWb k r z) {l : Fin r} {D : Set (Mx k r)} {f : Mx k r → E} (hL : LeftEq k r z l.castSucc D f)
    {g : Mx k r} (hg : g ∈ Glev k r l.castSucc ∩ D) (X : Mx k r) (hS : InS k r l (g * X * g⁻¹))
    (hk : Hpk k r * (g * X * g⁻¹)ᴴ * Hpk k r = -(g * X * g⁻¹)) :
    RdV X f g = (Complex.I * (((cStd * ell k r z (g * X * g⁻¹)).re : ℝ) : ℂ)) • f g := by sorry
