-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_Q_EabGlW_hpart_decomp
-- name    : Formalism.FourierDecayAlt.Q.EabGlW.hpart_decomp
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T16:44:50.844077+00:00
-- url     : https://prove2.me/theorems/ea581df0-adb6-4fef-90ad-4cf1faf2635e
-- title:
--   Eab Gl W: hpart decomp
-- statement:
--   The Eab Gl W construction uses the hpart decomp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GeneralLinearLevel/HpartUnique.lean#L212-L219
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GeneralLinearLevel/HpartUnique.lean#L212-L219

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

theorem Formalism.FourierDecayAlt.Q.EabGlW.hpart_decomp (Z : Mx k r) : Z = hpart1 (Hpk k r) Z + Complex.I • hpart2 (Hpk k r) Z := by sorry
