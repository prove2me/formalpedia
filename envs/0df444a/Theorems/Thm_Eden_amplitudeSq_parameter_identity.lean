-- Prove2me | Theorems.Thm_Eden_amplitudeSq_parameter_identity
-- name    : Eden.amplitudeSq_parameter_identity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:04:18.959352+00:00
-- url     : https://prove2.me/theorems/00cfbaa3-1bb3-45b0-92d5-aa2881d63fc7
-- title:
--   Eden: amplitude Sq parameter identity
-- statement:
--   Differentiating `s B(t,s) = S(t,s)` gives the radial derivative identity
--   without division by the initial radius, so it remains valid at `s=0`.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/InitialDerivative.lean#L48-L58
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/InitialDerivative.lean#L48-L58

import Definitions.Def_Eden_Evolution
import Definitions.Def_Eden_InitialDerivative
set_option autoImplicit true
noncomputable section
open Eden

theorem Eden.amplitudeSq_parameter_identity {t : ℝ} (ht : 0 ≤ t) (s : ℝ) :
    amplitudeSq t s + s * deriv (amplitudeSq t) s =
      Real.exp (-4 * t) / Real.sqrt (radialDiscriminant t s) ^ 3 := by sorry
