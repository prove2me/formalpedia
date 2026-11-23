-- Prove2me | Theorems.Thm_Formalism_GrowthSums_summable_min_div_pow_two_mul_add_one
-- name    : Formalism.GrowthSums.summable_min_div_pow_two_mul_add_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:53:47.98741+00:00
-- url     : https://prove2.me/theorems/871fd624-2415-40cb-8540-5c70a240687d
-- title:
--   Growth Sums: summable min div pow two mul add one
-- statement:
--   The Growth Sums construction uses the summable min div pow two mul add one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GrowthSums/FactorialBaseGrowth/PathBasisOfCount.lean#L10-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GrowthSums/FactorialBaseGrowth/PathBasisOfCount.lean#L10-L21

import Definitions.Def_Formalism_GrowthSums_StatementG
import Definitions.Def_Formalism_GrowthSums_FactorialBaseGrowth_PathBasisOfCount
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.GrowthSums

theorem Formalism.GrowthSums.summable_min_div_pow_two_mul_add_one {n : ℕ} (p : ℝ) (hp : 1 < p) (a : ℝ) (ha : 0 ≤ a)
    (cap : ZMod n → ℝ) (hcap : ∀ s, 0 ≤ cap s) (s : ZMod n) :
    Summable (fun e : ℕ => min (a / p ^ (2 * e + 1)) (cap (s + ((2 * e + 1 : ℕ) : ZMod n)))) := by sorry
