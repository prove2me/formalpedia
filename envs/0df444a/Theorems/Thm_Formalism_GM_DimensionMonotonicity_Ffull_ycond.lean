-- Prove2me | Theorems.Thm_Formalism_GM_DimensionMonotonicity_Ffull_ycond
-- name    : Formalism.GM.DimensionMonotonicity.Ffull_ycond
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T22:27:57.05552+00:00
-- url     : https://prove2.me/theorems/b3e50c3e-b18b-4c57-919c-ccaeb50e6297
-- title:
--   Dimension Monotonicity: Ffull ycond
-- statement:
--   The Dimension Monotonicity construction uses the Ffull ycond property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WeightSpaceDimensionMonotone.lean#L2192-L2225
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WeightSpaceDimensionMonotone.lean#L2192-L2225

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

theorem Formalism.GM.DimensionMonotonicity.Ffull_ycond [NeZero r] (ρ : Fin r) (n : Fin T.t → ℕ) (w : Fin r → ℤ)
    (f : MvPolynomial (Fin (T.pos i + 1) × Fin r) ℚ_[p])
    (hf : f ∈ MMw p ((LL.setTies T n).takeD (T.pos i + 1)) T.J (T.thrUpTo i) ρ w)
    (hS : ((LL.setTies T n).takeD (T.pos i + 1)).total ≤ n i) (k : Fin T.q) (hk : T.J k ≤ T.pos i + 1) :
    T.Ffull p (LL.setTies T n) i ρ (n i) f ∈ YCond p LL (T.J k) (T.thr k) := by sorry
