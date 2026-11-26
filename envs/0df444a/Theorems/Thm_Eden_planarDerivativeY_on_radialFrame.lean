-- Prove2me | Theorems.Thm_Eden_planarDerivativeY_on_radialFrame
-- name    : Eden.planarDerivativeY_on_radialFrame
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:16:40.965104+00:00
-- url     : https://prove2.me/theorems/81246818-0b5e-5d1c-9eb6-f1c8d1c4873c
-- title:
--   Eden: planar Derivative Y on radial Frame
-- statement:
--   The Eden construction uses the planar Derivative Y on radial Frame property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/DerivativeFrames.lean#L87-L99
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/DerivativeFrames.lean#L87-L99

import Definitions.Def_Eden_CartesianDerivative
import Definitions.Def_Eden_GrowthRates
import Definitions.Def_Eden_OrthogonalFrames
import Definitions.Def_Eden_DerivativeFrames
set_option autoImplicit true
noncomputable section
open Eden

theorem Eden.planarDerivativeY_on_radialFrame (Ω : ℝ) {t : ℝ} (ht : 0 ≤ t)
    (a b r u v : ℝ) (hab : a ^ 2 + b ^ 2 = 1) :
    planarDerivativeY Ω t (r * a) (r * b) (a * u - b * v) (b * u + a * v) =
      (a * (radialAmplitude t (r ^ 2) * u) - b * (planarAmplitude t (r ^ 2) * v)) *
          Real.sin (Ω * t) +
        (b * (radialAmplitude t (r ^ 2) * u) + a * (planarAmplitude t (r ^ 2) * v)) *
          Real.cos (Ω * t) := by sorry
