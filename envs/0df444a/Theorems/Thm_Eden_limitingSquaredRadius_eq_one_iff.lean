-- Prove2me | Theorems.Thm_Eden_limitingSquaredRadius_eq_one_iff
-- name    : Eden.limitingSquaredRadius_eq_one_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:51:57.389241+00:00
-- url     : https://prove2.me/theorems/47883ed8-2563-559d-afe0-22467885048b
-- title:
--   Eden: limiting Squared Radius eq one iff
-- statement:
--   The Eden construction uses the limiting Squared Radius eq one iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/SpectrumTable.lean#L31-L34
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/SpectrumTable.lean#L31-L34

import Definitions.Def_Eden_KaplanYorke
import Definitions.Def_Eden_SpectrumTable
set_option autoImplicit true
noncomputable section
open Eden

theorem Eden.limitingSquaredRadius_eq_one_iff (s : ℝ) : limitingSquaredRadius s = 1 ↔ s = 1 := by sorry
