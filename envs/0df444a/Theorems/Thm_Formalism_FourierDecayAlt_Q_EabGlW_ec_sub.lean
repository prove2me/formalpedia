-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_Q_EabGlW_ec_sub
-- name    : Formalism.FourierDecayAlt.Q.EabGlW.ec_sub
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T16:44:20.860909+00:00
-- url     : https://prove2.me/theorems/faebb11e-f99f-4b55-8315-073b95fb3436
-- title:
--   Eab Gl W: ec sub
-- statement:
--   The Eab Gl W construction uses the ec sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GeneralLinearLevel/ElementaryGeneratorsLevelGroup.lean#L66-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GeneralLinearLevel/ElementaryGeneratorsLevelGroup.lean#L66-L75

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

theorem Formalism.FourierDecayAlt.Q.EabGlW.ec_sub {i : Fin (r + 1)} {A B : Mx k r} (hA : Good k r i A) (hB : Good k r i B)
    {f F : Mx k r → E} {U : Set (Mx k r)} (hL : LocExt (Glev k r i) f F U) {g : Mx k r}
    (hg : g ∈ U) (hgG : g ∈ Glev k r i) :
    Ec (A - B) f g = Ec A f g - Ec B f g := by sorry
