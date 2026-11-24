-- Prove2me | Theorems.Thm_Formalism_GM_DimensionMonotonicity_inclusion_prodMap_injective
-- name    : Formalism.GM.DimensionMonotonicity.inclusion_prodMap_injective
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T22:26:42.478517+00:00
-- url     : https://prove2.me/theorems/9ed78adb-1067-4647-8786-a1b41ec9e237
-- title:
--   Dimension Monotonicity: inclusion prod Map injective
-- statement:
--   The Dimension Monotonicity construction uses the inclusion prod Map injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WeightSpaceDimensionMonotone.lean#L1974-L1978
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WeightSpaceDimensionMonotone.lean#L1974-L1978

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

theorem Formalism.GM.DimensionMonotonicity.inclusion_prodMap_injective [NeZero N] {K : ℕ} (hK : K + 1 ≤ N) :
    Function.Injective (fun x : Fin (K + 1) × Fin r => (ιF N K x.1, x.2)) := by sorry
