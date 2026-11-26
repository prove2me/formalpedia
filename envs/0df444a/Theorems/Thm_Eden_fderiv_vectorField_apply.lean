-- Prove2me | Theorems.Thm_Eden_fderiv_vectorField_apply
-- name    : Eden.fderiv_vectorField_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:26:06.998574+00:00
-- url     : https://prove2.me/theorems/122474b3-42e2-5e3e-8d32-064a614d8940
-- title:
--   Eden: fderiv vector Field apply
-- statement:
--   The full ambient Jacobian applied to a direction, with no radius or parameter
--   restriction. All components are those of the derivative.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/VectorFieldDerivative.lean#L62-L92
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/VectorFieldDerivative.lean#L62-L92

import Definitions.Def_Eden_CartesianDerivative
import Mathlib.LinearAlgebra.Trace
import Definitions.Def_Eden_VectorFieldDerivative
set_option autoImplicit true
noncomputable section
open Eden

theorem Eden.fderiv_vectorField_apply (c : ℝ) (p v : PhaseSpace) :
    fderiv ℝ (vectorField c) p v =
      !₂[q (radiusSq₁ p) * v 0 + 2 * deriv q (radiusSq₁ p) *
          (p 0 * v 0 + p 1 * v 1) * p 0 - v 1,
        q (radiusSq₁ p) * v 1 + 2 * deriv q (radiusSq₁ p) *
          (p 0 * v 0 + p 1 * v 1) * p 1 + v 0,
        q (radiusSq₂ p) * v 2 + 2 * deriv q (radiusSq₂ p) *
          (p 2 * v 2 + p 3 * v 3) * p 2 - Real.sqrt 2 * v 3,
        q (radiusSq₂ p) * v 3 + 2 * deriv q (radiusSq₂ p) *
          (p 2 * v 2 + p 3 * v 3) * p 3 + Real.sqrt 2 * v 2,
        -c * v 4] := by sorry
