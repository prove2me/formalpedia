-- Prove2me | Theorems.Thm_Formalism_GM_DimensionMonotonicity_glAct_mul_kill
-- name    : Formalism.GM.DimensionMonotonicity.glAct_mul_kill
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:26:23.275453+00:00
-- url     : https://prove2.me/theorems/3b166d61-3287-48b5-9c0e-c38667832ac7
-- title:
--   Dimension Monotonicity: gl Act mul kill
-- statement:
--   The Dimension Monotonicity construction uses the gl Act mul kill property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WeightSpaceDimensionMonotone.lean#L1264-L1274
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WeightSpaceDimensionMonotone.lean#L1264-L1274

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

theorem Formalism.GM.DimensionMonotonicity.glAct_mul_kill (LL : Letters N) (j : ℕ) (c d : Fin r) (x : MvPolynomial (Fin N × Fin r) ℚ_[p])
    {q : MvPolynomial (Fin N × Fin r) ℚ_[p]}
    (hq : ∀ m ∈ q.support, ∀ v : Fin N × Fin r, (v.1 : ℕ) < j → m v = 0) :
    glAct p LL j c d (x * q) = glAct p LL j c d x * q := by sorry
