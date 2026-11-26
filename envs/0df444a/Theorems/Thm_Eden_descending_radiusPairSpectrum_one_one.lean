-- Prove2me | Theorems.Thm_Eden_descending_radiusPairSpectrum_one_one
-- name    : Eden.descending_radiusPairSpectrum_one_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:52:20.399109+00:00
-- url     : https://prove2.me/theorems/d432daa2-58f3-5214-9041-fd7b43b7c270
-- title:
--   Eden: descending radius Pair Spectrum one one
-- statement:
--   The Eden construction uses the descending radius Pair Spectrum one one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/SpectrumTable.lean#L93-L102
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/SpectrumTable.lean#L93-L102

import Definitions.Def_Eden_KaplanYorke
import Definitions.Def_Eden_SpectrumTable
set_option autoImplicit true
noncomputable section
open Eden

theorem Eden.descending_radiusPairSpectrum_one_one {c : ℝ} (hc : 4 < c) :
    descending (radiusPairSpectrum c 1 1) = ![2, 2, 0, 0, -c] := by sorry
