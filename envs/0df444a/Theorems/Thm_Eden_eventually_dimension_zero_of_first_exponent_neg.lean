-- Prove2me | Theorems.Thm_Eden_eventually_dimension_zero_of_first_exponent_neg
-- name    : Eden.eventually_dimension_zero_of_first_exponent_neg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:59:56.872588+00:00
-- url     : https://prove2.me/theorems/bbd1edc8-1846-45f9-8df7-50868e36b8b4
-- title:
--   Eden: eventually dimension zero of first exponent neg
-- statement:
--   The Eden construction uses the eventually dimension zero of first exponent neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/EventualDimensionFormulas.lean#L59-L72
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/EventualDimensionFormulas.lean#L59-L72

import Definitions.Def_Eden_DimensionConvergence
import Definitions.Def_Eden_EventualDimensionFormulas
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden

theorem Eden.eventually_dimension_zero_of_first_exponent_neg (c : ℝ) (p : PhaseSpace)
    (hlim : lyapunovExponent c p 0 < 0) :
    ∀ᶠ t in atTop, (∀ i, normalizedLogSingularValues c t p i < 0) ∧
      finiteTimeDimension c t p = 0 := by sorry
