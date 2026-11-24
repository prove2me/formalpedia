-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_Q_EabGlW_hpart2_sub
-- name    : Formalism.FourierDecayAlt.Q.EabGlW.hpart2_sub
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T16:45:06.293063+00:00
-- url     : https://prove2.me/theorems/62f612a0-bfee-4254-8eb8-a65bd97776c7
-- title:
--   Eab Gl W: hpart2 sub
-- statement:
--   The Eab Gl W construction uses the hpart2 sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GeneralLinearLevel/ElementaryGeneratorsLevelGroup.lean#L61-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GeneralLinearLevel/ElementaryGeneratorsLevelGroup.lean#L61-L64

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

theorem Formalism.FourierDecayAlt.Q.EabGlW.hpart2_sub (A B : Mx k r) :
    hpart2 (Hpk k r) (A - B) = hpart2 (Hpk k r) A - hpart2 (Hpk k r) B := by sorry
