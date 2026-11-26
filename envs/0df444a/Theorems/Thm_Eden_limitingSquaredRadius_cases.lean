-- Prove2me | Theorems.Thm_Eden_limitingSquaredRadius_cases
-- name    : Eden.limitingSquaredRadius_cases
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:51:19.787962+00:00
-- url     : https://prove2.me/theorems/2c1546df-c9b9-4d63-8e4e-a78cdf086f9d
-- title:
--   Eden: limiting Squared Radius cases
-- statement:
--   The Eden construction uses the limiting Squared Radius cases property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/SpectrumTable.lean#L25-L29
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/SpectrumTable.lean#L25-L29

import Definitions.Def_Eden_KaplanYorke
import Definitions.Def_Eden_SpectrumTable
set_option autoImplicit true
noncomputable section
open Eden

theorem Eden.limitingSquaredRadius_cases (s : ℝ) :
    limitingSquaredRadius s = 0 ∨ limitingSquaredRadius s = 1 ∨ limitingSquaredRadius s = 2 := by sorry
