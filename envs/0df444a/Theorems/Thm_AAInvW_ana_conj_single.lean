-- Prove2me | Theorems.Thm_AAInvW_ana_conj_single
-- name    : AAInvW.ana_conj_single
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T17:29:42.472872+00:00
-- url     : https://prove2.me/theorems/5774aaa5-6897-4aa4-ba24-7fca5b558e6a
-- title:
--   AAInv W: ana conj single
-- statement:
--   The AAInv W construction uses the ana conj single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdjointInverseTranslate/ConjugatedGeneratorGlRelation.lean#L203-L207
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdjointInverseTranslate/ConjugatedGeneratorGlRelation.lean#L203-L207

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

theorem AAInvW.ana_conj_single (s : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) :
    s⁻¹ * Matrix.single a b (1 : ℂ) * s = ∑ c, ∑ d, (s⁻¹ c a * s b d) • Matrix.single c d (1 : ℂ) := by sorry
