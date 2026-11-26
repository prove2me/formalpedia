-- Prove2me | Theorems.Thm_Eden_spectrumEntry_at_kaplanYorkeIndex_neg
-- name    : Eden.spectrumEntry_at_kaplanYorkeIndex_neg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:46:28.237043+00:00
-- url     : https://prove2.me/theorems/593c7dfe-b168-440c-8da2-78a8fab11da5
-- title:
--   Eden: spectrum Entry at kaplan Yorke Index neg
-- statement:
--   The next exponent is strictly negative whenever the index is below five.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/KaplanYorke.lean#L74-L80
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/KaplanYorke.lean#L74-L80

import Definitions.Def_Eden_LyapunovExponents
import Mathlib.Data.Finset.Max
import Definitions.Def_Eden_KaplanYorke
set_option autoImplicit true
noncomputable section
open Eden

theorem Eden.spectrumEntry_at_kaplanYorkeIndex_neg {a : Fin 5 → ℝ}
    (hj : kaplanYorkeIndex a < 5) : spectrumEntry a (kaplanYorkeIndex a) < 0 := by sorry
