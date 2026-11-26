-- Prove2me | Theorems.Thm_Eden_fderiv_evolution_radialFrame
-- name    : Eden.fderiv_evolution_radialFrame
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:17:24.334118+00:00
-- url     : https://prove2.me/theorems/6f712916-9ab3-57f0-a307-2c0e449451d4
-- title:
--   Eden: fderiv evolution radial Frame
-- statement:
--   Action of the derivative on the whole initial orthonormal frame.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/DerivativeDecomposition.lean#L42-L72
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/DerivativeDecomposition.lean#L42-L72

import Definitions.Def_Eden_DerivativeFrames
import Definitions.Def_Eden_DerivativeDecomposition
set_option autoImplicit true
noncomputable section
open Eden

theorem Eden.fderiv_evolution_radialFrame (c : ℝ) {t : ℝ} (ht : 0 ≤ t) (p v : PhaseSpace) :
    fderiv ℝ (evolution c t) p (radialFrame p v) =
      angularRotation t (radialFrame p (diagonalLinear (derivativeFactors c t p) v)) := by sorry
