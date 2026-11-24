-- Prove2me | Theorems.Thm_AAInvW_ana_rdAdd
-- name    : AAInvW.ana_rdAdd
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T15:56:18.557477+00:00
-- url     : https://prove2.me/theorems/7fb59943-8826-43ac-90e7-48efe3a2424a
-- title:
--   AAInv W: ana rd Add
-- statement:
--   The AAInv W construction uses the ana rd Add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdjointInverseTranslate/SmoothLinear.lean#L117-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdjointInverseTranslate/SmoothLinear.lean#L117-L121

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_AnaHpartUnique
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_SmoothLinear
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

theorem AAInvW.ana_rdAdd (hH : HInvol H) {f : Matrix (Fin n) (Fin n) ℂ → E} {A B g : Matrix (Fin n) (Fin n) ℂ}
    (hf : SmoothOnH H f) (hA : inLH H A) (hB : inLH H B) (hg : inUH H g) :
    RdV (A + B) f g = RdV A f g + RdV B f g := by sorry
