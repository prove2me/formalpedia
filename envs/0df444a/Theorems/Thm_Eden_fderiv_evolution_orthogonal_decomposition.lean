-- Prove2me | Theorems.Thm_Eden_fderiv_evolution_orthogonal_decomposition
-- name    : Eden.fderiv_evolution_orthogonal_decomposition
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:17:47.810276+00:00
-- url     : https://prove2.me/theorems/62196ef7-43ee-42c8-977f-91ae17877922
-- title:
--   Eden: fderiv evolution orthogonal decomposition
-- statement:
--   Orthogonal-diagonal-orthogonal factorisation of the derivative,
--   with input radial frame fixed by the initial point.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/DerivativeDecomposition.lean#L76-L85
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/DerivativeDecomposition.lean#L76-L85

import Definitions.Def_Eden_DerivativeFrames
import Definitions.Def_Eden_DerivativeDecomposition
set_option autoImplicit true
noncomputable section
open Eden

theorem Eden.fderiv_evolution_orthogonal_decomposition (c : ℝ) {t : ℝ} (ht : 0 ≤ t)
    (p : PhaseSpace) :
    (fderiv ℝ (evolution c t) p).toLinearMap =
      (angularRotation t).toLinearEquiv.toLinearMap ∘ₗ
        (radialFrame p).toLinearEquiv.toLinearMap ∘ₗ
          diagonalLinear (derivativeFactors c t p) ∘ₗ
            (radialFrame p).symm.toLinearEquiv.toLinearMap := by sorry
