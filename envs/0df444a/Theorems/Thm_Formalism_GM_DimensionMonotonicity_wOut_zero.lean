-- Prove2me | Theorems.Thm_Formalism_GM_DimensionMonotonicity_wOut_zero
-- name    : Formalism.GM.DimensionMonotonicity.wOut_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:37:04.403374+00:00
-- url     : https://prove2.me/theorems/0ddd8926-0e45-4b10-9b76-b79e94d5ffd7
-- title:
--   Dimension Monotonicity: w Out zero
-- statement:
--   The Dimension Monotonicity construction uses the w Out zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WeightSpaceDimensionMonotone.lean#L1678-L1688
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WeightSpaceDimensionMonotone.lean#L1678-L1688

import Definitions.Def_Formalism_MahlerMeasure_StatementTM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeY
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeBij
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeInto
import Mathlib
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.DimensionMonotonicity
open MvPolynomial Finset Formalism.GM.M
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}

theorem Formalism.GM.DimensionMonotonicity.wOut_zero {i0 : Fin N} {m : Fin N × Fin r →₀ ℕ} (h : Finsupp.weight (wOut N r i0) m = 0) :
    ∀ v : Fin N × Fin r, v.1 ≠ i0 → m v = 0 := by sorry
