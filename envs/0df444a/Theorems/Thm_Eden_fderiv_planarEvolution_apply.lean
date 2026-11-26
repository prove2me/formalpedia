-- Prove2me | Theorems.Thm_Eden_fderiv_planarEvolution_apply
-- name    : Eden.fderiv_planarEvolution_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:27:05.145811+00:00
-- url     : https://prove2.me/theorems/b0c0f5c3-6fb3-5518-88ed-0272858d9431
-- title:
--   Eden: fderiv planar Evolution apply
-- statement:
--   The Eden construction uses the fderiv planar Evolution apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PlanarDerivative.lean#L46-L63
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PlanarDerivative.lean#L46-L63

import Definitions.Def_Eden_PlanarVectorField
import Definitions.Def_Eden_DerivativeFrames
import Definitions.Def_Eden_PlanarDerivative
set_option autoImplicit true
noncomputable section
open Eden

theorem Eden.fderiv_planarEvolution_apply (Ω : ℝ) {t : ℝ} (ht : 0 ≤ t) (p v : PlanarSpace) :
    fderiv ℝ (planarEvolution Ω t) p v =
      !₂[planarDerivativeX Ω t (p 0) (p 1) (v 0) (v 1),
        planarDerivativeY Ω t (p 0) (p 1) (v 0) (v 1)] := by sorry
