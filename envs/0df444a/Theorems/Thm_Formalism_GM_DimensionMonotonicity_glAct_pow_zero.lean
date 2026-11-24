-- Prove2me | Theorems.Thm_Formalism_GM_DimensionMonotonicity_glAct_pow_zero
-- name    : Formalism.GM.DimensionMonotonicity.glAct_pow_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:36:28.662842+00:00
-- url     : https://prove2.me/theorems/7aed1acd-a6d0-4a35-ab14-95cb9dfe9406
-- title:
--   Dimension Monotonicity: gl Act pow zero
-- statement:
--   The Dimension Monotonicity construction uses the gl Act pow zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WeightSpaceDimensionMonotone.lean#L1819-L1824
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WeightSpaceDimensionMonotone.lean#L1819-L1824

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

theorem Formalism.GM.DimensionMonotonicity.glAct_pow_zero {N r : ℕ} {p : ℕ} [Fact p.Prime] (LL : Letters N) (j : ℕ) (c d : Fin r)
    {x : MvPolynomial (Fin N × Fin r) ℚ_[p]} (hx : glAct p LL j c d x = 0) (k : ℕ) :
    glAct p LL j c d (x ^ k) = 0 := by sorry
