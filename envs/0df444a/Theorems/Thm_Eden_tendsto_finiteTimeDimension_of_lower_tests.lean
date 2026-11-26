-- Prove2me | Theorems.Thm_Eden_tendsto_finiteTimeDimension_of_lower_tests
-- name    : Eden.tendsto_finiteTimeDimension_of_lower_tests
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:55:19.406869+00:00
-- url     : https://prove2.me/theorems/adeb6d9e-333a-40cf-b534-7e2995277a10
-- title:
--   Eden: tendsto finite Time Dimension of lower tests
-- statement:
--   The Eden construction uses the tendsto finite Time Dimension of lower tests property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/DimensionConvergenceCriteria.lean#L44-L59
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/DimensionConvergenceCriteria.lean#L44-L59

import Definitions.Def_Eden_FiniteTimeKaplanYorke
import Definitions.Def_Eden_DimensionConvergenceCriteria
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden

theorem Eden.tendsto_finiteTimeDimension_of_lower_tests (c : ℝ) (p : PhaseSpace)
    (hlo : ∀ d ∈ Ioo 0 (asymptoticDimension c p),
      ∀ᶠ t in atTop, d ≤ finiteTimeDimension c t p) :
    Tendsto (fun t => finiteTimeDimension c t p) atTop (𝓝 (asymptoticDimension c p)) := by sorry
