-- Prove2me | Theorems.Thm_Eden_fderiv_planarVectorField_apply
-- name    : Eden.fderiv_planarVectorField_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:26:26.814807+00:00
-- url     : https://prove2.me/theorems/bb49f99c-984f-5e2c-808e-35b694c9ff0f
-- title:
--   Eden: fderiv planar Vector Field apply
-- statement:
--   The Eden construction uses the fderiv planar Vector Field apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PlanarVectorField.lean#L28-L47
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PlanarVectorField.lean#L28-L47

import Definitions.Def_Eden_VectorFieldDerivative
import Definitions.Def_Eden_PlanarVectorField
set_option autoImplicit true
noncomputable section
open Eden

theorem Eden.fderiv_planarVectorField_apply (Ω : ℝ) (p v : PlanarSpace) :
    fderiv ℝ (planarVectorField Ω) p v =
      !₂[q (p 0 ^ 2 + p 1 ^ 2) * v 0 + 2 * deriv q (p 0 ^ 2 + p 1 ^ 2) *
          (p 0 * v 0 + p 1 * v 1) * p 0 - Ω * v 1,
        q (p 0 ^ 2 + p 1 ^ 2) * v 1 + 2 * deriv q (p 0 ^ 2 + p 1 ^ 2) *
          (p 0 * v 0 + p 1 * v 1) * p 1 + Ω * v 0] := by sorry
