-- Prove2me | Theorems.Thm_Formalism_GM_DimensionMonotonicity_glAct_freezeSub_gen
-- name    : Formalism.GM.DimensionMonotonicity.glAct_freezeSub_gen
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:47:35.377071+00:00
-- url     : https://prove2.me/theorems/b7e869b1-fcdb-4c70-8582-885e953e4394
-- title:
--   Dimension Monotonicity: gl Act freeze Sub gen
-- statement:
--   The Dimension Monotonicity construction uses the gl Act freeze Sub gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WeightSpaceDimensionMonotone.lean#L1829-L1854
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WeightSpaceDimensionMonotone.lean#L1829-L1854

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
open Formalism.GM.M.FB

theorem Formalism.GM.DimensionMonotonicity.glAct_freezeSub_gen (LL : Letters K) (n : ℕ) (ρ a b : Fin r) (ha : a ≠ ρ) (hb : b ≠ ρ)
    (v : Fin K × Fin r) :
    glAct p (LL.snoc n) (K + 1) a b (freezeSub p LL ρ v) = aeval (freezeSub p LL ρ) (glAct p LL K a b (X v)) := by sorry
