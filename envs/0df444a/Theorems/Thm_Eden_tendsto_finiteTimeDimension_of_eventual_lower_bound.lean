-- Prove2me | Theorems.Thm_Eden_tendsto_finiteTimeDimension_of_eventual_lower_bound
-- name    : Eden.tendsto_finiteTimeDimension_of_eventual_lower_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:55:46.618599+00:00
-- url     : https://prove2.me/theorems/cf62cb75-d661-4217-9732-7eb50d7ad2e5
-- title:
--   Eden: tendsto finite Time Dimension of eventual lower bound
-- statement:
--   The Eden construction uses the tendsto finite Time Dimension of eventual lower bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/DimensionConvergenceCriteria.lean#L76-L82
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/DimensionConvergenceCriteria.lean#L76-L82

import Definitions.Def_Eden_FiniteTimeKaplanYorke
import Definitions.Def_Eden_DimensionConvergenceCriteria
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden

theorem Eden.tendsto_finiteTimeDimension_of_eventual_lower_bound (c : ℝ) (p : PhaseSpace)
    (hlo : ∀ᶠ t in atTop, asymptoticDimension c p ≤ finiteTimeDimension c t p) :
    Tendsto (fun t => finiteTimeDimension c t p) atTop (𝓝 (asymptoticDimension c p)) := by sorry
