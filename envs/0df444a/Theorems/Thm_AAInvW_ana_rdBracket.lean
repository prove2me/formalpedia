-- Prove2me | Theorems.Thm_AAInvW_ana_rdBracket
-- name    : AAInvW.ana_rdBracket
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T17:29:36.443699+00:00
-- url     : https://prove2.me/theorems/c2b2031d-8a6c-400e-a3e8-70ffdd662e57
-- title:
--   AAInv W: ana rd Bracket
-- statement:
--   The AAInv W construction uses the ana rd Bracket property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdjointInverseTranslate/ConjugatedGeneratorGlRelation.lean#L22-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdjointInverseTranslate/ConjugatedGeneratorGlRelation.lean#L22-L51

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

theorem AAInvW.ana_rdBracket (hH : HInvol H) {f : Matrix (Fin n) (Fin n) ℂ → E} {X Y g : Matrix (Fin n) (Fin n) ℂ}
    (hf : SmoothOnH H f) (hX : inLH H X) (hY : inLH H Y) (hg : inUH H g) :
    RdV X (RdV Y f) g - RdV Y (RdV X f) g = RdV (X * Y - Y * X) f g := by sorry
