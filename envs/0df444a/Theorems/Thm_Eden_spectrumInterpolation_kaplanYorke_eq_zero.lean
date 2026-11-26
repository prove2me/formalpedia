-- Prove2me | Theorems.Thm_Eden_spectrumInterpolation_kaplanYorke_eq_zero
-- name    : Eden.spectrumInterpolation_kaplanYorke_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:10:34.228094+00:00
-- url     : https://prove2.me/theorems/4aa83f61-e448-5fbc-b02b-18e849b76626
-- title:
--   Eden: spectrum Interpolation kaplan Yorke eq zero
-- statement:
--   The Eden construction uses the spectrum Interpolation kaplan Yorke eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/EventualDimensionFormulas.lean#L16-L36
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/EventualDimensionFormulas.lean#L16-L36

import Definitions.Def_Eden_DimensionConvergence
import Definitions.Def_Eden_EventualDimensionFormulas
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden

theorem Eden.spectrumInterpolation_kaplanYorke_eq_zero {a : Fin 5 → ℝ}
    (hj : kaplanYorkeIndex a < 5) :
    spectrumInterpolation a (kaplanYorkeDimension a) = 0 := by sorry
