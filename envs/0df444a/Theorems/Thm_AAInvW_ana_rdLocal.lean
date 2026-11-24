-- Prove2me | Theorems.Thm_AAInvW_ana_rdLocal
-- name    : AAInvW.ana_rdLocal
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T15:56:43.70694+00:00
-- url     : https://prove2.me/theorems/3a281c6a-3632-4f14-9266-0ba127f48573
-- title:
--   AAInv W: ana rd Local
-- statement:
--   The AAInv W construction uses the ana rd Local property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdjointInverseTranslate/SmoothLinear.lean#L129-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdjointInverseTranslate/SmoothLinear.lean#L129-L134

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

theorem AAInvW.ana_rdLocal (hH : HInvol H) {f f' : Matrix (Fin n) (Fin n) ℂ → E} {X g : Matrix (Fin n) (Fin n) ℂ}
    (hff : ∀ x, inUH H x → f x = f' x) (hX : inLH H X) (hg : inUH H g) : RdV X f g = RdV X f' g := by sorry
