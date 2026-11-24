-- Prove2me | Theorems.Thm_AAInvW_ana_Ec_sub
-- name    : AAInvW.ana_Ec_sub
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T17:29:22.344968+00:00
-- url     : https://prove2.me/theorems/088c6bc9-9554-4ad4-89e7-dcfa01a7e92b
-- title:
--   AAInv W: ana Ec sub
-- statement:
--   The AAInv W construction uses the ana Ec sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdjointInverseTranslate/ConjugatedGeneratorGlRelation.lean#L53-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdjointInverseTranslate/ConjugatedGeneratorGlRelation.lean#L53-L60

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_SmoothLinear
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_ConjugatedGeneratorGlRelation
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
open AAInvW
open Formalism.REAL Formalism.QuantumDeterminants
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {H : Matrix (Fin n) (Fin n) ℂ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem AAInvW.ana_Ec_sub (hH : HInvol H) {f : Matrix (Fin n) (Fin n) ℂ → E} {g : Matrix (Fin n) (Fin n) ℂ}
    (hf : SmoothOnH H f) (hg : inUH H g) (Z W : Matrix (Fin n) (Fin n) ℂ) :
    EcH H (Z - W) f g = EcH H Z f g - EcH H W f g := by sorry
