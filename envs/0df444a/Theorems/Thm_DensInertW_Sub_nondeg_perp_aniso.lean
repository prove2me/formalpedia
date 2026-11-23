-- Prove2me | Theorems.Thm_DensInertW_Sub_nondeg_perp_aniso
-- name    : DensInertW.Sub.nondeg_perp_aniso
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T09:38:06.025715+00:00
-- url     : https://prove2.me/theorems/8c56e610-b17b-416a-b956-01dd55ff5a2f
-- title:
--   Sub: nondeg perp aniso
-- statement:
--   The Sub construction uses the nondeg perp aniso property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InertDensity/FinrankInfKerAddOne.lean#L132-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InertDensity/FinrankInfKerAddOne.lean#L132-L144

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

theorem DensInertW.Sub.nondeg_perp_aniso (hadd : ∀ a b : L, (a + b) ^ q = a ^ q + b ^ q)
    (W : Submodule L (Fin n → L)) (hW : NonDeg q M W) (e : Fin n → L) (he : e ∈ W)
    (hee : hf q M e e ≠ 0) : NonDeg q M (W ⊓ LinearMap.ker (hfL q M e)) := by sorry
