-- Prove2me | Theorems.Thm_Formalism_GM_DimensionMonotonicity_Ffull_step
-- name    : Formalism.GM.DimensionMonotonicity.Ffull_step
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:45:52.562804+00:00
-- url     : https://prove2.me/theorems/5c21c782-b114-4695-b207-4eadbdd3cc0e
-- title:
--   Dimension Monotonicity: Ffull step
-- statement:
--   The Dimension Monotonicity construction uses the Ffull step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WeightSpaceDimensionMonotone.lean#L2227-L2248
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WeightSpaceDimensionMonotone.lean#L2227-L2248

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

theorem Formalism.GM.DimensionMonotonicity.Ffull_step (ρ : Fin r) (n : Fin T.t → ℕ) (n' : ℕ) (hn : n i ≤ n')
    (f : MvPolynomial (Fin (T.pos i + 1) × Fin r) ℚ_[p])
    (hS : ((LL.setTies T n).takeD (T.pos i + 1)).total ≤ n i) :
    T.Ffull p (LL.setTies T (Function.update n i n')) i ρ n' f =
      X (⟨T.pos i + 1, by have := hK_of_adm LL T hadm i; omega⟩, ρ) ^ (n' - n i) *
        T.Ffull p (LL.setTies T n) i ρ (n i) f := by sorry
