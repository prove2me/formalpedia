-- Prove2me | Theorems.Thm_Eden_kaplanYorkeDimension_formula_of_index_lt_five
-- name    : Eden.kaplanYorkeDimension_formula_of_index_lt_five
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:57:06.016047+00:00
-- url     : https://prove2.me/theorems/4434102b-beb6-4e79-b62f-4265c43eb952
-- title:
--   Eden: kaplan Yorke Dimension formula of index lt five
-- statement:
--   The Eden construction uses the kaplan Yorke Dimension formula of index lt five property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/InterpolationSign.lean#L64-L71
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/InterpolationSign.lean#L64-L71

import Definitions.Def_Eden_LogarithmicInterpolation
import Definitions.Def_Eden_InterpolationSign
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.kaplanYorkeDimension_formula_of_index_lt_five {a : Fin 5 → ℝ}
    (hj : kaplanYorkeIndex a < 5) :
    kaplanYorkeDimension a = (kaplanYorkeIndex a : ℝ) +
      spectrumPartialSum a (kaplanYorkeIndex a) / -spectrumEntry a (kaplanYorkeIndex a) := by sorry
