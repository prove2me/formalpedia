-- Prove2me | Theorems.Thm_Formalism_GM_DimensionMonotonicity_Ffull_pol
-- name    : Formalism.GM.DimensionMonotonicity.Ffull_pol
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T22:27:42.134077+00:00
-- url     : https://prove2.me/theorems/48cfcbc1-af77-4fad-adcc-1cb4b808d833
-- title:
--   Dimension Monotonicity: Ffull pol
-- statement:
--   The Dimension Monotonicity construction uses the Ffull pol property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WeightSpaceDimensionMonotone.lean#L2146-L2190
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WeightSpaceDimensionMonotone.lean#L2146-L2190

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
variable [NeZero N] (LL : Letters N) (T : TieData) (hadm : T.Admissible LL) (i : Fin T.t)
include hadm

theorem Formalism.GM.DimensionMonotonicity.Ffull_pol (ρ : Fin r) (n : Fin T.t → ℕ) (f : MvPolynomial (Fin (T.pos i + 1) × Fin r) ℚ_[p])
    (hfP : f ∈ Pol p r ((LL.setTies T n).takeD (T.pos i + 1)))
    (hS : ((LL.setTies T n).takeD (T.pos i + 1)).total ≤ n i) :
    T.Ffull p (LL.setTies T n) i ρ (n i) f ∈ Pol p r (Lz (LL.setTies T n) (T.pos i + 1 + 1)) := by sorry
