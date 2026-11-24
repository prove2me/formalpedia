-- Prove2me | Theorems.Thm_Formalism_GM_DimensionMonotonicity_Ffull_eq
-- name    : Formalism.GM.DimensionMonotonicity.Ffull_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:26:10.045815+00:00
-- url     : https://prove2.me/theorems/02801417-960d-4b40-ae28-02c693eb6e0a
-- title:
--   Dimension Monotonicity: Ffull eq
-- statement:
--   The Dimension Monotonicity construction uses the Ffull eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WeightSpaceDimensionMonotone.lean#L1980-L1983
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WeightSpaceDimensionMonotone.lean#L1980-L1983

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

theorem Formalism.GM.DimensionMonotonicity.Ffull_eq [NeZero N] (LL : Letters N) (T : TieData) (i : Fin T.t) (ρ : Fin r) (n : ℕ)
    (f : MvPolynomial (Fin (T.pos i + 1) × Fin r) ℚ_[p]) :
    T.Ffull p LL i ρ n f = rename (fun x => (ιF N (T.pos i + 1) x.1, x.2)) (freeze p (LL.takeD (T.pos i + 1)) ρ n f) := by sorry
