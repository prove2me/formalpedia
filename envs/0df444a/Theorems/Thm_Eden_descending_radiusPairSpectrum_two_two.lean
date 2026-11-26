-- Prove2me | Theorems.Thm_Eden_descending_radiusPairSpectrum_two_two
-- name    : Eden.descending_radiusPairSpectrum_two_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:52:47.103309+00:00
-- url     : https://prove2.me/theorems/df8c0197-fb1c-43ba-a336-fb6eb52cc186
-- title:
--   Eden: descending radius Pair Spectrum two two
-- statement:
--   The Eden construction uses the descending radius Pair Spectrum two two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/SpectrumTable.lean#L115-L124
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/SpectrumTable.lean#L115-L124

import Definitions.Def_Eden_KaplanYorke
import Definitions.Def_Eden_SpectrumTable
set_option autoImplicit true
noncomputable section
open Eden

theorem Eden.descending_radiusPairSpectrum_two_two {c : ℝ} (hc : 4 < c) :
    descending (radiusPairSpectrum c 2 2) = ![0, 0, -4, -4, -c] := by sorry
