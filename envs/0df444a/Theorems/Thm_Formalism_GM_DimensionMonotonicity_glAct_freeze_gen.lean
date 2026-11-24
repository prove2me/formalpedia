-- Prove2me | Theorems.Thm_Formalism_GM_DimensionMonotonicity_glAct_freeze_gen
-- name    : Formalism.GM.DimensionMonotonicity.glAct_freeze_gen
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:27:19.010694+00:00
-- url     : https://prove2.me/theorems/139d58bc-79aa-45cc-adee-c325f8af4b75
-- title:
--   Dimension Monotonicity: gl Act freeze gen
-- statement:
--   The Dimension Monotonicity construction uses the gl Act freeze gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WeightSpaceDimensionMonotone.lean#L1856-L1867
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WeightSpaceDimensionMonotone.lean#L1856-L1867

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
variable {p : ℕ} [Fact p.Prime] {K r : ℕ}

theorem Formalism.GM.DimensionMonotonicity.glAct_freeze_gen (LL : Letters K) (n : ℕ) (ρ a b : Fin r) (ha : a ≠ ρ) (hb : b ≠ ρ)
    (f : MvPolynomial (Fin K × Fin r) ℚ_[p]) :
    glAct p (LL.snoc n) (K + 1) a b (freeze p LL ρ n f) = freeze p LL ρ n (glAct p LL K a b f) := by sorry
