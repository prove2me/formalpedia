-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_Q_LeftMultiplicationRule_core
-- name    : Formalism.FourierDecayAlt.Q.LeftMultiplicationRule.core
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T15:28:21.801003+00:00
-- url     : https://prove2.me/theorems/67275eaf-f91e-4194-b923-3fc77744f29e
-- title:
--   Left Multiplication Rule: core
-- statement:
--   The Left Multiplication Rule construction uses the core property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LeftPhaseRule/HasDerivAtPhase.lean#L191-L234
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LeftPhaseRule/HasDerivAtPhase.lean#L191-L234

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

theorem Formalism.FourierDecayAlt.Q.LeftMultiplicationRule.core {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {z : Fin (2 * r + k + 1) → ℂ}
    (hz : inWb k r z) {l : Fin r} {D : Set (Mx k r)} {f : Mx k r → E} (hL : LeftEq k r z l.castSucc D f)
    {g : Mx k r} (hg : g ∈ Glev k r l.castSucc ∩ D) (a b : Fin (2 * r + k + 1))
    (hS : InS k r l (g * Matrix.single a b 1 * g⁻¹)) :
    EH k r a b f g = (ell k r z (g * Matrix.single a b 1 * g⁻¹) +
      star (ell k r z (Hpk k r * (g * Matrix.single a b 1 * g⁻¹)ᴴ * Hpk k r))) • f g := by sorry
