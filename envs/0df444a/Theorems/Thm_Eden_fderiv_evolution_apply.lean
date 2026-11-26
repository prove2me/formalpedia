-- Prove2me | Theorems.Thm_Eden_fderiv_evolution_apply
-- name    : Eden.fderiv_evolution_apply
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T13:08:50.371843+00:00
-- url     : https://prove2.me/theorems/32730ee3-e36b-5911-97cd-f45cc1d3a55b
-- title:
--   Eden: fderiv evolution apply
-- statement:
--   Every coordinate of the five-dimensional Fréchet derivative.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/CartesianDerivative.lean#L68-L94
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/CartesianDerivative.lean#L68-L94

import Definitions.Def_Eden_InitialDerivative
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Definitions.Def_Eden_CartesianDerivative
set_option autoImplicit true
noncomputable section
open Eden

theorem Eden.fderiv_evolution_apply (c : ℝ) {t : ℝ} (ht : 0 ≤ t) (p v : PhaseSpace) :
    fderiv ℝ (evolution c t) p v =
      !₂[planarDerivativeX 1 t (p 0) (p 1) (v 0) (v 1),
         planarDerivativeY 1 t (p 0) (p 1) (v 0) (v 1),
         planarDerivativeX (Real.sqrt 2) t (p 2) (p 3) (v 2) (v 3),
         planarDerivativeY (Real.sqrt 2) t (p 2) (p 3) (v 2) (v 3),
         Real.exp (-c * t) * v 4] := by sorry
