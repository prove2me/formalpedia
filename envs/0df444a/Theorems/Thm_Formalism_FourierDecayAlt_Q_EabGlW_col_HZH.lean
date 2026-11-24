-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_Q_EabGlW_col_HZH
-- name    : Formalism.FourierDecayAlt.Q.EabGlW.col_HZH
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T16:45:55.75096+00:00
-- url     : https://prove2.me/theorems/6936ff0e-c991-4d2d-84c4-da1ced824e16
-- title:
--   Eab Gl W: col HZH
-- statement:
--   The Eab Gl W construction uses the col HZH property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GeneralLinearLevel/HpartUnique.lean#L168-L187
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GeneralLinearLevel/HpartUnique.lean#L168-L187

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

theorem Formalism.FourierDecayAlt.Q.EabGlW.col_HZH {i : Fin (r + 1)} {Z : Mx k r} (hZ : InV k r i Z) {q : Fin (2 * r + k + 1)}
    (hq : Out k r i q) (p : Fin (2 * r + k + 1)) : (Hpk k r * Zᴴ * Hpk k r) p q = 0 := by sorry
