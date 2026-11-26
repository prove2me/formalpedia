-- Prove2me | Theorems.Thm_Eden_descending_radiusPairSpectrum_zero_two
-- name    : Eden.descending_radiusPairSpectrum_zero_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:52:15.300852+00:00
-- url     : https://prove2.me/theorems/8994fa62-1ead-4198-aa28-fb622dd4779b
-- title:
--   Eden: descending radius Pair Spectrum zero two
-- statement:
--   The Eden construction uses the descending radius Pair Spectrum zero two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/SpectrumTable.lean#L82-L91
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/SpectrumTable.lean#L82-L91

import Definitions.Def_Eden_KaplanYorke
import Definitions.Def_Eden_SpectrumTable
set_option autoImplicit true
noncomputable section
open Eden

theorem Eden.descending_radiusPairSpectrum_zero_two {c : ℝ} (hc : 4 < c) :
    descending (radiusPairSpectrum c 0 2) = ![0, -2, -2, -4, -c] := by sorry
