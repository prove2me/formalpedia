-- Prove2me | Theorems.Thm_Formalism_GM_DimensionMonotonicity_Ffull_hw
-- name    : Formalism.GM.DimensionMonotonicity.Ffull_hw
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T22:26:59.666168+00:00
-- url     : https://prove2.me/theorems/50ee62a9-840b-4b40-bfaf-ae007990523d
-- title:
--   Dimension Monotonicity: Ffull hw
-- statement:
--   The Dimension Monotonicity construction uses the Ffull hw property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WeightSpaceDimensionMonotone.lean#L2077-L2116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WeightSpaceDimensionMonotone.lean#L2077-L2116

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

theorem Formalism.GM.DimensionMonotonicity.Ffull_hw [NeZero r] (ρ : Fin r) (hρ : (ρ : ℕ) = r - 1) (n : Fin T.t → ℕ) (w : Fin r → ℤ)
    (f : MvPolynomial (Fin (T.pos i + 1) × Fin r) ℚ_[p])
    (hf : f ∈ MMw p ((LL.setTies T n).takeD (T.pos i + 1)) T.J (T.thrUpTo i) ρ w)
    (hS : ((LL.setTies T n).takeD (T.pos i + 1)).total ≤ n i) :
    (GA p LL (T.pos i + 1 + 1)).IsHW (w - ((n i : ℕ) : ℤ) • Pi.single ρ 1) (T.Ffull p (LL.setTies T n) i ρ (n i) f) := by sorry
