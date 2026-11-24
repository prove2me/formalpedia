-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_Q_EabGlW_skew_conj
-- name    : Formalism.FourierDecayAlt.Q.EabGlW.skew_conj
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T15:35:59.121486+00:00
-- url     : https://prove2.me/theorems/8f27b782-042a-4181-b9f4-502239661fa9
-- title:
--   Eab Gl W: skew conj
-- statement:
--   The Eab Gl W construction uses the skew conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GeneralLinearLevel/HpartUnique.lean#L37-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GeneralLinearLevel/HpartUnique.lean#L37-L42

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

theorem Formalism.FourierDecayAlt.Q.EabGlW.skew_conj {X : Mx k r} (h : Skew X) : Xᴴ = Hpk k r * (-X) * Hpk k r := by sorry
