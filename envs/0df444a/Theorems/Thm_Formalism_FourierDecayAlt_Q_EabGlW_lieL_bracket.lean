-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_Q_EabGlW_lieL_bracket
-- name    : Formalism.FourierDecayAlt.Q.EabGlW.lieL_bracket
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T16:41:38.16908+00:00
-- url     : https://prove2.me/theorems/de273bb6-7eff-4795-a4e8-e820661cc57e
-- title:
--   Eab Gl W: lie L bracket
-- statement:
--   The Eab Gl W construction uses the lie L bracket property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GeneralLinearLevel/HpartUnique.lean#L115-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GeneralLinearLevel/HpartUnique.lean#L115-L130

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

theorem Formalism.FourierDecayAlt.Q.EabGlW.lieL_bracket {i : Fin (r + 1)} {X Y : Mx k r} (hX : X ∈ LieL k r i) (hY : Y ∈ LieL k r i) :
    X * Y - Y * X ∈ LieL k r i := by sorry
