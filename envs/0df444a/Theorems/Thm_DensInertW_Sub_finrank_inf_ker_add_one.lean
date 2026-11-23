-- Prove2me | Theorems.Thm_DensInertW_Sub_finrank_inf_ker_add_one
-- name    : DensInertW.Sub.finrank_inf_ker_add_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:39:12.86169+00:00
-- url     : https://prove2.me/theorems/69e87252-5cf3-4494-937d-549541f78267
-- title:
--   Sub: finrank inf ker add one
-- statement:
--   The Sub construction uses the finrank inf ker add one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InertDensity/FinrankInfKerAddOne.lean#L103-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InertDensity/FinrankInfKerAddOne.lean#L103-L119

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

theorem DensInertW.Sub.finrank_inf_ker_add_one (W : Submodule L (Fin n → L)) (f : (Fin n → L) →ₗ[L] L)
    (u : Fin n → L) (hu : u ∈ W) (hfu : f u ≠ 0) :
    finrank L ↥(W ⊓ LinearMap.ker f) + 1 = finrank L ↥W := by sorry
