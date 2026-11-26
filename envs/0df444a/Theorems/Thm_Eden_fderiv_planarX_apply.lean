-- Prove2me | Theorems.Thm_Eden_fderiv_planarX_apply
-- name    : Eden.fderiv_planarX_apply
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T13:05:20.136996+00:00
-- url     : https://prove2.me/theorems/8bbe8e2d-de2d-53d0-8e66-385b9d87f5aa
-- title:
--   Eden: fderiv planar X apply
-- statement:
--   The Eden construction uses the fderiv planar X apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/CartesianDerivative.lean#L35-L48
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/CartesianDerivative.lean#L35-L48

import Definitions.Def_Eden_InitialDerivative
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Definitions.Def_Eden_CartesianDerivative
set_option autoImplicit true
noncomputable section
open Eden
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {f g : E → ℝ} {f' g' : E →L[ℝ] ℝ} {p : E}

theorem Eden.fderiv_planarX_apply (Ω : ℝ) {t : ℝ} (ht : 0 ≤ t)
    (hf : HasFDerivAt f f' p) (hg : HasFDerivAt g g' p) (v : E) :
    fderiv ℝ (fun u => planarX Ω t (f u) (g u)) p v =
      planarDerivativeX Ω t (f p) (g p) (f' v) (g' v) := by sorry
