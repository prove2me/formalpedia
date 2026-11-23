-- Prove2me | Theorems.Thm_DensInertW_Sub_hf_symm
-- name    : DensInertW.Sub.hf_symm
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T00:19:34.953476+00:00
-- url     : https://prove2.me/theorems/f407f73f-12f8-48dd-87a7-cd23094d8c54
-- title:
--   Sub: hf symm
-- statement:
--   The Sub construction uses the hf symm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InertDensity/FinrankInfKerAddOne.lean#L71-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InertDensity/FinrankInfKerAddOne.lean#L71-L80

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

theorem DensInertW.Sub.hf_symm (hadd : ∀ a b : L, (a + b) ^ q = a ^ q + b ^ q) (hinv : ∀ a : L, (a ^ q) ^ q = a)
    (hM : ∀ k l, M l k = M k l ^ q) (x y : Fin n → L) : hf q M y x = (hf q M x y) ^ q := by sorry
