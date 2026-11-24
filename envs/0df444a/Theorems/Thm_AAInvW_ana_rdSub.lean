-- Prove2me | Theorems.Thm_AAInvW_ana_rdSub
-- name    : AAInvW.ana_rdSub
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T15:50:44.118799+00:00
-- url     : https://prove2.me/theorems/0046790e-aba5-40df-8fb4-a316eb0c4e8f
-- title:
--   AAInv W: ana rd Sub
-- statement:
--   The AAInv W construction uses the ana rd Sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdjointInverseTranslate/SmoothLinear.lean#L123-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdjointInverseTranslate/SmoothLinear.lean#L123-L127

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

theorem AAInvW.ana_rdSub (hH : HInvol H) {f : Matrix (Fin n) (Fin n) ℂ → E} {A B g : Matrix (Fin n) (Fin n) ℂ}
    (hf : SmoothOnH H f) (hA : inLH H A) (hB : inLH H B) (hg : inUH H g) :
    RdV (A - B) f g = RdV A f g - RdV B f g := by sorry
