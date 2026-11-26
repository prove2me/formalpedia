-- Prove2me | Theorems.Thm_Eden_kaplanYorkeDimension_of_index_five
-- name    : Eden.kaplanYorkeDimension_of_index_five
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:46:15.330509+00:00
-- url     : https://prove2.me/theorems/ca18a954-f4fb-5bd2-8c11-d4f374b4b7db
-- title:
--   Eden: kaplan Yorke Dimension of index five
-- statement:
--   The Eden construction uses the kaplan Yorke Dimension of index five property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/KaplanYorke.lean#L97-L99
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/KaplanYorke.lean#L97-L99

import Definitions.Def_Eden_LyapunovExponents
import Mathlib.Data.Finset.Max
import Definitions.Def_Eden_KaplanYorke
set_option autoImplicit true
noncomputable section
open Eden

theorem Eden.kaplanYorkeDimension_of_index_five {a : Fin 5 → ℝ}
    (hj : kaplanYorkeIndex a = 5) : kaplanYorkeDimension a = 5 := by sorry
