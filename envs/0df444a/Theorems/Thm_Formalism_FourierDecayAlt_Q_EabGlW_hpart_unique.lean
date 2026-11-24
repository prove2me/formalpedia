-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_Q_EabGlW_hpart_unique
-- name    : Formalism.FourierDecayAlt.Q.EabGlW.hpart_unique
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T16:45:25.47003+00:00
-- url     : https://prove2.me/theorems/0e01174f-7086-4bc1-805b-837fdace33ab
-- title:
--   Eab Gl W: hpart unique
-- statement:
--   The Eab Gl W construction uses the hpart unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GeneralLinearLevel/HpartUnique.lean#L221-L242
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GeneralLinearLevel/HpartUnique.lean#L221-L242

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GeneralLinearLevel_ExpMulVecFix
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FormalDegreeBessel_FinalIO
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GeneralLinearLevel_HpartUnique
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.EabGlW
open Formalism.REAL Formalism.QuantumDeterminants
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}

theorem Formalism.FourierDecayAlt.Q.EabGlW.hpart_unique {P Q : Mx k r} (hP : Skew P) (hQ : Skew Q) :
    hpart1 (Hpk k r) (P + Complex.I • Q) = P ∧ hpart2 (Hpk k r) (P + Complex.I • Q) = Q := by sorry
