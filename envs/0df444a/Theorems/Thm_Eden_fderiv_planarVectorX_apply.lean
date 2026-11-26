-- Prove2me | Theorems.Thm_Eden_fderiv_planarVectorX_apply
-- name    : Eden.fderiv_planarVectorX_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:20:15.652742+00:00
-- url     : https://prove2.me/theorems/a391017f-81b5-556f-ba17-9240a70a0b34
-- title:
--   Eden: fderiv planar Vector X apply
-- statement:
--   The Eden construction uses the fderiv planar Vector X apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/VectorFieldDerivative.lean#L32-L43
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/VectorFieldDerivative.lean#L32-L43

import Definitions.Def_Eden_CartesianDerivative
import Mathlib.LinearAlgebra.Trace
import Definitions.Def_Eden_VectorFieldDerivative
set_option autoImplicit true
noncomputable section
open Eden
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {f g : E → ℝ} {f' g' : E →L[ℝ] ℝ} {p : E}

theorem Eden.fderiv_planarVectorX_apply (Ω : ℝ)
    (hf : HasFDerivAt f f' p) (hg : HasFDerivAt g g' p) (v : E) :
    fderiv ℝ (fun u => q (f u ^ 2 + g u ^ 2) * f u - Ω * g u) p v =
      q (f p ^ 2 + g p ^ 2) * f' v +
        2 * deriv q (f p ^ 2 + g p ^ 2) * (f p * f' v + g p * g' v) * f p - Ω * g' v := by sorry
