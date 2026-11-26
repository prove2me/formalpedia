-- Prove2me | Theorems.Thm_Eden_descending_radiusPairSpectrum_zero_zero
-- name    : Eden.descending_radiusPairSpectrum_zero_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:51:53.995587+00:00
-- url     : https://prove2.me/theorems/5a5a81e4-edc4-5019-b3dd-5b6f6052702a
-- title:
--   Eden: descending radius Pair Spectrum zero zero
-- statement:
--   The Eden construction uses the descending radius Pair Spectrum zero zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/SpectrumTable.lean#L62-L69
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/SpectrumTable.lean#L62-L69

import Definitions.Def_Eden_KaplanYorke
import Definitions.Def_Eden_SpectrumTable
set_option autoImplicit true
noncomputable section
open Eden

theorem Eden.descending_radiusPairSpectrum_zero_zero {c : ℝ} (hc : 4 < c) :
    descending (radiusPairSpectrum c 0 0) = ![-2, -2, -2, -2, -c] := by sorry
