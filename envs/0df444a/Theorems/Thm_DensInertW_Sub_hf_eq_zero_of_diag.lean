-- Prove2me | Theorems.Thm_DensInertW_Sub_hf_eq_zero_of_diag
-- name    : DensInertW.Sub.hf_eq_zero_of_diag
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:37:55.017419+00:00
-- url     : https://prove2.me/theorems/cb4432c7-d497-485a-8a1a-881601be3b48
-- title:
--   Sub: hf eq zero of diag
-- statement:
--   The Sub construction uses the hf eq zero of diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InertDensity/FinrankInfKerAddOne.lean#L87-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InertDensity/FinrankInfKerAddOne.lean#L87-L101

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

theorem DensInertW.Sub.hf_eq_zero_of_diag (hadd : ∀ a b : L, (a + b) ^ q = a ^ q + b ^ q)
    (hinv : ∀ a : L, (a ^ q) ^ q = a) (hM : ∀ k l, M l k = M k l ^ q)
    (htr : ∀ z : L, z ≠ 0 → ∃ c : L, c * z + (c * z) ^ q ≠ 0)
    (W : Submodule L (Fin n → L)) (h0 : ∀ v ∈ W, hf q M v v = 0) :
    ∀ x ∈ W, ∀ y ∈ W, hf q M x y = 0 := by sorry
