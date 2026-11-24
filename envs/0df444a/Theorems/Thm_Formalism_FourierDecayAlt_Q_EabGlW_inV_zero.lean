-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_Q_EabGlW_inV_zero
-- name    : Formalism.FourierDecayAlt.Q.EabGlW.inV_zero
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T16:41:24.469506+00:00
-- url     : https://prove2.me/theorems/fbe641f5-c27b-4553-ab1f-aec6fe86780d
-- title:
--   Eab Gl W: in V zero
-- statement:
--   The Eab Gl W construction uses the in V zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GeneralLinearLevel/ElementaryGeneratorsLevelGroup.lean#L80-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GeneralLinearLevel/ElementaryGeneratorsLevelGroup.lean#L80-L80

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GeneralLinearLevel_HpartUnique
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GeneralLinearLevel_ElementaryGeneratorsLevelGroup
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
variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem Formalism.FourierDecayAlt.Q.EabGlW.inV_zero {i : Fin (r + 1)} : InV k r i (0 : Mx k r) := by sorry
