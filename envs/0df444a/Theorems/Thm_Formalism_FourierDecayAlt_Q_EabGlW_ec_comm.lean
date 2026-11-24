-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_Q_EabGlW_ec_comm
-- name    : Formalism.FourierDecayAlt.Q.EabGlW.ec_comm
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T16:44:40.653615+00:00
-- url     : https://prove2.me/theorems/e06c486f-db1a-4272-8f10-d52cd1ef9117
-- title:
--   Eab Gl W: ec comm
-- statement:
--   The Eab Gl W construction uses the ec comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GeneralLinearLevel/ElementaryGeneratorsLevelGroup.lean#L22-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GeneralLinearLevel/ElementaryGeneratorsLevelGroup.lean#L22-L54

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

theorem Formalism.FourierDecayAlt.Q.EabGlW.ec_comm {i : Fin (r + 1)} {Z W : Mx k r} (hZ : Good k r i Z) (hW : Good k r i W)
    {f F : Mx k r → E} {U : Set (Mx k r)} (hL : LocExt (Glev k r i) f F U) {g : Mx k r}
    (hg : g ∈ U) (hgG : g ∈ Glev k r i) :
    Ec Z (Ec W f) g - Ec W (Ec Z f) g = Ec (Z * W - W * Z) f g := by sorry
