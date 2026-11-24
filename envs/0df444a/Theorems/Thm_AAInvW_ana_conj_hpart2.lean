-- Prove2me | Theorems.Thm_AAInvW_ana_conj_hpart2
-- name    : AAInvW.ana_conj_hpart2
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T17:29:28.422742+00:00
-- url     : https://prove2.me/theorems/fc1e8a5a-34d0-4b22-9692-5474d0826c9f
-- title:
--   AAInv W: ana conj hpart2
-- statement:
--   The AAInv W construction uses the ana conj hpart2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdjointInverseTranslate/ConjugatedGeneratorGlRelation.lean#L159-L167
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdjointInverseTranslate/ConjugatedGeneratorGlRelation.lean#L159-L167

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

theorem AAInvW.ana_conj_hpart2 (hH : HInvol H) {s : Matrix (Fin n) (Fin n) ℂ} (hs : inUH H s)
    (Z : Matrix (Fin n) (Fin n) ℂ) : s⁻¹ * hpart2 H Z * s = hpart2 H (s⁻¹ * Z * s) := by sorry
