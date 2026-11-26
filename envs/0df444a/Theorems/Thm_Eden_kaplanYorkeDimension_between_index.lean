-- Prove2me | Theorems.Thm_Eden_kaplanYorkeDimension_between_index
-- name    : Eden.kaplanYorkeDimension_between_index
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:47:42.473803+00:00
-- url     : https://prove2.me/theorems/73408157-663e-4214-99a6-e0c19a630876
-- title:
--   Eden: kaplan Yorke Dimension between index
-- statement:
--   In the middle branch the dimension lies in the unit interval beginning
--   at the largest nonnegative partial-sum index, with a strict upper endpoint.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/KaplanYorke.lean#L108-L124
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/KaplanYorke.lean#L108-L124

import Definitions.Def_Eden_LyapunovExponents
import Mathlib.Data.Finset.Max
import Definitions.Def_Eden_KaplanYorke
set_option autoImplicit true
noncomputable section
open Eden

theorem Eden.kaplanYorkeDimension_between_index {a : Fin 5 → ℝ}
    (hj₀ : 0 < kaplanYorkeIndex a) (hj₅ : kaplanYorkeIndex a < 5) :
    (kaplanYorkeIndex a : ℝ) ≤ kaplanYorkeDimension a ∧
      kaplanYorkeDimension a < (kaplanYorkeIndex a : ℝ) + 1 := by sorry
