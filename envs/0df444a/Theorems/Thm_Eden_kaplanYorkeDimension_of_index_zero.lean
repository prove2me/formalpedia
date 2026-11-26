-- Prove2me | Theorems.Thm_Eden_kaplanYorkeDimension_of_index_zero
-- name    : Eden.kaplanYorkeDimension_of_index_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:46:26.542568+00:00
-- url     : https://prove2.me/theorems/ec10d1c7-9d3e-41d2-9086-f07575e68ab0
-- title:
--   Eden: kaplan Yorke Dimension of index zero
-- statement:
--   The Eden construction uses the kaplan Yorke Dimension of index zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/KaplanYorke.lean#L93-L95
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/KaplanYorke.lean#L93-L95

import Definitions.Def_Eden_LyapunovExponents
import Mathlib.Data.Finset.Max
import Definitions.Def_Eden_KaplanYorke
set_option autoImplicit true
noncomputable section
open Eden

theorem Eden.kaplanYorkeDimension_of_index_zero {a : Fin 5 → ℝ}
    (hj : kaplanYorkeIndex a = 0) : kaplanYorkeDimension a = 0 := by sorry
