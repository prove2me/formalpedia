-- Prove2me | Theorems.Thm_Eden_finiteTimeDimension_eq_kaplanYorke
-- name    : Eden.finiteTimeDimension_eq_kaplanYorke
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:53:15.352798+00:00
-- url     : https://prove2.me/theorems/7b8d893c-0171-4164-988d-fa2f94e3f905
-- title:
--   Eden: finite Time Dimension eq kaplan Yorke
-- statement:
--   At every positive real time, the dimension defined from the ambient derivative equals the Kaplan--Yorke formula applied to its ordered
--   singular-value logarithms divided by time.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/FiniteTimeKaplanYorke.lean#L49-L56
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/FiniteTimeKaplanYorke.lean#L49-L56

import Definitions.Def_Eden_InterpolationSign
import Definitions.Def_Eden_FiniteTimeKaplanYorke
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.finiteTimeDimension_eq_kaplanYorke (c : ℝ) {t : ℝ} (ht : 0 < t)
    (p : PhaseSpace) :
    finiteTimeDimension c t p =
      kaplanYorkeDimension (normalizedLogSingularValues c t p) := by sorry
