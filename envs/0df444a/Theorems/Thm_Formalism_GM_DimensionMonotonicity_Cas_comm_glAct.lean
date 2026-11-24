-- Prove2me | Theorems.Thm_Formalism_GM_DimensionMonotonicity_Cas_comm_glAct
-- name    : Formalism.GM.DimensionMonotonicity.Cas_comm_glAct
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:45:40.867685+00:00
-- url     : https://prove2.me/theorems/d61a59ee-32a9-46be-8c9a-35d9a7670342
-- title:
--   Dimension Monotonicity: Cas comm gl Act
-- statement:
--   The Dimension Monotonicity construction uses the Cas comm gl Act property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WeightSpaceDimensionMonotone.lean#L1608-L1619
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WeightSpaceDimensionMonotone.lean#L1608-L1619

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

theorem Formalism.GM.DimensionMonotonicity.Cas_comm_glAct (LL : Letters N) {j0 J : ℕ} (hJ : j0 ≤ J) (c d : Fin r) (F : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    (GA p LL j0).Cas (glAct p LL J c d F) = glAct p LL J c d ((GA p LL j0).Cas F) := by sorry
