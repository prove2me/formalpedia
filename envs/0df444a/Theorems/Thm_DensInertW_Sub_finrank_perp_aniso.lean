-- Prove2me | Theorems.Thm_DensInertW_Sub_finrank_perp_aniso
-- name    : DensInertW.Sub.finrank_perp_aniso
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:39:22.630022+00:00
-- url     : https://prove2.me/theorems/d07db1f0-f51c-4e81-8f05-01a60d6e2ac4
-- title:
--   Sub: finrank perp aniso
-- statement:
--   The Sub construction uses the finrank perp aniso property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InertDensity/FinrankInfKerAddOne.lean#L121-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InertDensity/FinrankInfKerAddOne.lean#L121-L124

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_AnisoPeelAlt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_FinrankInfKerAddOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Module
open DensInertW DensInertW.Sub
variable {L : Type} [Field L]
variable {n : ℕ} {q : ℕ} {M : Matrix (Fin n) (Fin n) L}

theorem DensInertW.Sub.finrank_perp_aniso (W : Submodule L (Fin n → L)) (e : Fin n → L) (he : e ∈ W)
    (hee : hf q M e e ≠ 0) :
    finrank L ↥(W ⊓ LinearMap.ker (hfL q M e)) + 1 = finrank L ↥W := by sorry
