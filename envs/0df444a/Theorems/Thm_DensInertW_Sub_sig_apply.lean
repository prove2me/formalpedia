-- Prove2me | Theorems.Thm_DensInertW_Sub_sig_apply
-- name    : DensInertW.Sub.sig_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:38:02.734823+00:00
-- url     : https://prove2.me/theorems/60d2b193-7c91-4936-80f3-2de59a6bf81f
-- title:
--   Sub: sig apply
-- statement:
--   The Sub construction uses the sig apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InertDensity/FinrankInfKerAddOne.lean#L22-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InertDensity/FinrankInfKerAddOne.lean#L22-L23

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

theorem DensInertW.Sub.sig_apply (q : ℕ) (hq : q ≠ 0) (hadd : ∀ a b : L, (a + b) ^ q = a ^ q + b ^ q) (a : L) :
    sig q hq hadd a = a ^ q := by sorry
