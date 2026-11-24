-- Prove2me | Theorems.Thm_Formalism_GM_DimensionMonotonicity_gSpan_eq
-- name    : Formalism.GM.DimensionMonotonicity.gSpan_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:27:23.600011+00:00
-- url     : https://prove2.me/theorems/e513c707-312f-490e-9e16-e88da2abd475
-- title:
--   Dimension Monotonicity: g Span eq
-- statement:
--   The Dimension Monotonicity construction uses the g Span eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WeightSpaceDimensionMonotone.lean#L2347-L2353
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WeightSpaceDimensionMonotone.lean#L2347-L2353

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

theorem Formalism.GM.DimensionMonotonicity.gSpan_eq (LL : Letters N) (T : TieData) (n : Fin T.t → ℕ) (j : ℕ) (F : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    gSpan p (LL.setTies T n) j F = (GA p LL j).gS {F} := by sorry
