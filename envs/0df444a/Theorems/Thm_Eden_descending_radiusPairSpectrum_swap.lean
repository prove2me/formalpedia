-- Prove2me | Theorems.Thm_Eden_descending_radiusPairSpectrum_swap
-- name    : Eden.descending_radiusPairSpectrum_swap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:48:08.024793+00:00
-- url     : https://prove2.me/theorems/f3ac89cf-3278-482e-a15d-dc95779c6edf
-- title:
--   Eden: descending radius Pair Spectrum swap
-- statement:
--   The Eden construction uses the descending radius Pair Spectrum swap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/SpectrumTable.lean#L36-L42
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/SpectrumTable.lean#L36-L42

import Definitions.Def_Eden_KaplanYorke
import Definitions.Def_Eden_SpectrumTable
set_option autoImplicit true
noncomputable section
open Eden

theorem Eden.descending_radiusPairSpectrum_swap (c s₁ s₂ : ℝ) :
    descending (radiusPairSpectrum c s₁ s₂) = descending (radiusPairSpectrum c s₂ s₁) := by sorry
