-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_Q_EabGlW_hpart_kill
-- name    : Formalism.FourierDecayAlt.Q.EabGlW.hpart_kill
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T15:36:04.14463+00:00
-- url     : https://prove2.me/theorems/cb15f46a-693d-4a1e-804c-1e1681595697
-- title:
--   Eab Gl W: hpart kill
-- statement:
--   The Eab Gl W construction uses the hpart kill property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GeneralLinearLevel/HpartUnique.lean#L189-L195
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GeneralLinearLevel/HpartUnique.lean#L189-L195

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

theorem Formalism.FourierDecayAlt.Q.EabGlW.hpart_kill {i : Fin (r + 1)} {Z : Mx k r} (hZ : InV k r i Z) {q : Fin (2 * r + k + 1)}
    (hq : Out k r i q) :
    hpart1 (Hpk k r) Z *ᵥ bvec q = 0 ∧ hpart2 (Hpk k r) Z *ᵥ bvec q = 0 := by sorry
