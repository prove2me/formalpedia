-- Prove2me | Theorems.Thm_Eden_eventually_finiteTimeDimension_lt
-- name    : Eden.eventually_finiteTimeDimension_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:57:36.593416+00:00
-- url     : https://prove2.me/theorems/92c0c646-a0d3-5a3e-ab62-fdece00ad516
-- title:
--   Eden: eventually finite Time Dimension lt
-- statement:
--   The Eden construction uses the eventually finite Time Dimension lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/DimensionConvergenceCriteria.lean#L22-L42
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/DimensionConvergenceCriteria.lean#L22-L42

import Definitions.Def_Eden_FiniteTimeKaplanYorke
import Definitions.Def_Eden_DimensionConvergenceCriteria
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden

theorem Eden.eventually_finiteTimeDimension_lt (c : ℝ) (p : PhaseSpace) {u : ℝ}
    (hu : asymptoticDimension c p < u) :
    ∀ᶠ t in atTop, finiteTimeDimension c t p < u := by sorry
