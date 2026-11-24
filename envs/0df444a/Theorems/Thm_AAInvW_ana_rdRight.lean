-- Prove2me | Theorems.Thm_AAInvW_ana_rdRight
-- name    : AAInvW.ana_rdRight
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T17:29:44.167834+00:00
-- url     : https://prove2.me/theorems/aadf177e-075b-43c6-bcec-cd6dbc20bbae
-- title:
--   AAInv W: ana rd Right
-- statement:
--   The AAInv W construction uses the ana rd Right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdjointInverseTranslate/ConjugatedGeneratorGlRelation.lean#L137-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdjointInverseTranslate/ConjugatedGeneratorGlRelation.lean#L137-L147

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

theorem AAInvW.ana_rdRight (hH : HInvol H) {f : Matrix (Fin n) (Fin n) ℂ → E} {X s g : Matrix (Fin n) (Fin n) ℂ}
    (hs : inUH H s) : RdV X (fun x => f (x * s)) g = RdV (s⁻¹ * X * s) f (g * s) := by sorry
