-- Prove2me | Theorems.Thm_Eden_fderiv_planarVectorY_apply
-- name    : Eden.fderiv_planarVectorY_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:20:28.145734+00:00
-- url     : https://prove2.me/theorems/c4754bec-190a-48da-9ae9-fafd1eac092f
-- title:
--   Eden: fderiv planar Vector Y apply
-- statement:
--   The Eden construction uses the fderiv planar Vector Y apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/VectorFieldDerivative.lean#L45-L56
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/VectorFieldDerivative.lean#L45-L56

import Definitions.Def_Eden_CartesianDerivative
import Mathlib.LinearAlgebra.Trace
import Definitions.Def_Eden_VectorFieldDerivative
set_option autoImplicit true
noncomputable section
open Eden
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {f g : E → ℝ} {f' g' : E →L[ℝ] ℝ} {p : E}

theorem Eden.fderiv_planarVectorY_apply (Ω : ℝ)
    (hf : HasFDerivAt f f' p) (hg : HasFDerivAt g g' p) (v : E) :
    fderiv ℝ (fun u => q (f u ^ 2 + g u ^ 2) * g u + Ω * f u) p v =
      q (f p ^ 2 + g p ^ 2) * g' v +
        2 * deriv q (f p ^ 2 + g p ^ 2) * (f p * f' v + g p * g' v) * g p + Ω * f' v := by sorry
