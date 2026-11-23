-- Prove2me | Theorems.Thm_DensInertW_cg_hf_right
-- name    : DensInertW.cg_hf_right
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:38:36.119811+00:00
-- url     : https://prove2.me/theorems/8b434760-687d-466f-9eb5-39d3f5af4e76
-- title:
--   Dens Inert W: cg hf right
-- statement:
--   The Dens Inert W construction uses the cg hf right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InertDensity/RepCountCongruenceInvariant.lean#L61-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InertDensity/RepCountCongruenceInvariant.lean#L61-L92

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

theorem DensInertW.cg_hf_right (K L : Type) [Field K] [Fintype K] [Field L] [Algebra K L] {m n : ℕ}
    (M : Matrix (Fin n) (Fin n) L) (c : Fin m → L) (x : Fin n → L) (y : Fin m → Fin n → L) :
    hf (Fintype.card K) M x (∑ l, c l • y l) =
      ∑ l, c l ^ Fintype.card K * hf (Fintype.card K) M x (y l) := by sorry
