-- Prove2me | Theorems.Thm_Eden_descending_radiusPairSpectrum_one_two
-- name    : Eden.descending_radiusPairSpectrum_one_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:52:23.367972+00:00
-- url     : https://prove2.me/theorems/f775fd58-1688-4b16-a176-7e849650c454
-- title:
--   Eden: descending radius Pair Spectrum one two
-- statement:
--   The Eden construction uses the descending radius Pair Spectrum one two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/SpectrumTable.lean#L104-L113
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/SpectrumTable.lean#L104-L113

import Definitions.Def_Eden_KaplanYorke
import Definitions.Def_Eden_SpectrumTable
set_option autoImplicit true
noncomputable section
open Eden

theorem Eden.descending_radiusPairSpectrum_one_two {c : ℝ} (hc : 4 < c) :
    descending (radiusPairSpectrum c 1 2) = ![2, 0, 0, -4, -c] := by sorry
