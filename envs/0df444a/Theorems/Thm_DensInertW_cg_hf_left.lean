-- Prove2me | Theorems.Thm_DensInertW_cg_hf_left
-- name    : DensInertW.cg_hf_left
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T09:38:49.032471+00:00
-- url     : https://prove2.me/theorems/11816585-694b-4702-a652-c4677d4d89eb
-- title:
--   Dens Inert W: cg hf left
-- statement:
--   The Dens Inert W construction uses the cg hf left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InertDensity/RepCountCongruenceInvariant.lean#L49-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InertDensity/RepCountCongruenceInvariant.lean#L49-L59

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_AnisoPeelAlt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_ExistsTraceNeZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_RepCountCongruenceInvariant
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open DensInertW

theorem DensInertW.cg_hf_left {L : Type} [Field L] {m n : ℕ} (q : ℕ) (M : Matrix (Fin n) (Fin n) L)
    (c : Fin m → L) (x : Fin m → Fin n → L) (y : Fin n → L) :
    hf q M (∑ k, c k • x k) y = ∑ k, c k * hf q M (x k) y := by sorry
