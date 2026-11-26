-- Prove2me | Theorems.Thm_Eden_fderiv_planarY_apply
-- name    : Eden.fderiv_planarY_apply
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T13:05:22.741267+00:00
-- url     : https://prove2.me/theorems/d4d5b796-04af-5cc0-ada7-b4e14ce1e5d2
-- title:
--   Eden: fderiv planar Y apply
-- statement:
--   The Eden construction uses the fderiv planar Y apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/CartesianDerivative.lean#L50-L63
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/CartesianDerivative.lean#L50-L63

import Definitions.Def_Eden_InitialDerivative
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Definitions.Def_Eden_CartesianDerivative
set_option autoImplicit true
noncomputable section
open Eden
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {f g : E → ℝ} {f' g' : E →L[ℝ] ℝ} {p : E}

theorem Eden.fderiv_planarY_apply (Ω : ℝ) {t : ℝ} (ht : 0 ≤ t)
    (hf : HasFDerivAt f f' p) (hg : HasFDerivAt g g' p) (v : E) :
    fderiv ℝ (fun u => planarY Ω t (f u) (g u)) p v =
      planarDerivativeY Ω t (f p) (g p) (f' v) (g' v) := by sorry
