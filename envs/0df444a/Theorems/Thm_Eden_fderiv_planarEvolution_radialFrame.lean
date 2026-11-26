-- Prove2me | Theorems.Thm_Eden_fderiv_planarEvolution_radialFrame
-- name    : Eden.fderiv_planarEvolution_radialFrame
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:27:03.43132+00:00
-- url     : https://prove2.me/theorems/5ff5ff8f-92ac-49aa-8a46-8ab5f0efbfe4
-- title:
--   Eden: fderiv planar Evolution radial Frame
-- statement:
--   The Eden construction uses the fderiv planar Evolution radial Frame property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PlanarDerivative.lean#L125-L142
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PlanarDerivative.lean#L125-L142

import Definitions.Def_Eden_PlanarVectorField
import Definitions.Def_Eden_DerivativeFrames
import Definitions.Def_Eden_PlanarDerivative
set_option autoImplicit true
noncomputable section
open Eden

theorem Eden.fderiv_planarEvolution_radialFrame (Ω : ℝ) {t : ℝ} (ht : 0 ≤ t) (p v : PlanarSpace) :
    fderiv ℝ (planarEvolution Ω t) p (planarRadialFrame p v) =
      planarAngularRotation Ω t (planarRadialFrame p (planarDiagonal (planarFactors t p) v)) := by sorry
