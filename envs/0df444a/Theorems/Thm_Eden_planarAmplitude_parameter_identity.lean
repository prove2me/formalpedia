-- Prove2me | Theorems.Thm_Eden_planarAmplitude_parameter_identity
-- name    : Eden.planarAmplitude_parameter_identity
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T13:07:32.323178+00:00
-- url     : https://prove2.me/theorems/f048b7eb-9521-46a8-a8f5-140676d47546
-- title:
--   Eden: planar Amplitude parameter identity
-- statement:
--   The radial derivative of `r ↦ r g(t,r²)` expressed through the derivative
--   of the amplitude with respect to squared radius. The identity includes zero.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/InitialDerivative.lean#L62-L76
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/InitialDerivative.lean#L62-L76

import Definitions.Def_Eden_Evolution
import Definitions.Def_Eden_InitialDerivative
set_option autoImplicit true
noncomputable section
open Eden

theorem Eden.planarAmplitude_parameter_identity {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) :
    planarAmplitude t s + 2 * s * deriv (planarAmplitude t) s =
      radialAmplitude t s := by sorry
