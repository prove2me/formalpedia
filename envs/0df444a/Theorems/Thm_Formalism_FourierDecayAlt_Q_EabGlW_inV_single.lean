-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_Q_EabGlW_inV_single
-- name    : Formalism.FourierDecayAlt.Q.EabGlW.inV_single
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T16:45:35.85011+00:00
-- url     : https://prove2.me/theorems/8dd58316-65a0-4b5a-9d48-f184237174d3
-- title:
--   Eab Gl W: in V single
-- statement:
--   The Eab Gl W construction uses the in V single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GeneralLinearLevel/ElementaryGeneratorsLevelGroup.lean#L82-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GeneralLinearLevel/ElementaryGeneratorsLevelGroup.lean#L82-L94

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

theorem Formalism.FourierDecayAlt.Q.EabGlW.inV_single {i : Fin (r + 1)} (x y : Fin (mdim k r i)) :
    InV k r i (Matrix.single (posL k r i x) (posL k r i y) (1 : ℂ)) := by sorry
