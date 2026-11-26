-- Prove2me | Theorems.Thm_Eden_planarDerivativeX_on_radialFrame
-- name    : Eden.planarDerivativeX_on_radialFrame
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:16:34.860806+00:00
-- url     : https://prove2.me/theorems/1d8f0662-a15f-55b7-9511-46b6cb387b89
-- title:
--   Eden: planar Derivative X on radial Frame
-- statement:
--   The Eden construction uses the planar Derivative X on radial Frame property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/DerivativeFrames.lean#L73-L85
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/DerivativeFrames.lean#L73-L85

import Definitions.Def_Eden_CartesianDerivative
import Definitions.Def_Eden_GrowthRates
import Definitions.Def_Eden_OrthogonalFrames
import Definitions.Def_Eden_DerivativeFrames
set_option autoImplicit true
noncomputable section
open Eden

theorem Eden.planarDerivativeX_on_radialFrame (Ω : ℝ) {t : ℝ} (ht : 0 ≤ t)
    (a b r u v : ℝ) (hab : a ^ 2 + b ^ 2 = 1) :
    planarDerivativeX Ω t (r * a) (r * b) (a * u - b * v) (b * u + a * v) =
      (a * (radialAmplitude t (r ^ 2) * u) - b * (planarAmplitude t (r ^ 2) * v)) *
          Real.cos (Ω * t) -
        (b * (radialAmplitude t (r ^ 2) * u) + a * (planarAmplitude t (r ^ 2) * v)) *
          Real.sin (Ω * t) := by sorry
