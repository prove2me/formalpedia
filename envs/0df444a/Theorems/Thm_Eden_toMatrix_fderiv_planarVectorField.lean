-- Prove2me | Theorems.Thm_Eden_toMatrix_fderiv_planarVectorField
-- name    : Eden.toMatrix_fderiv_planarVectorField
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:26:21.547807+00:00
-- url     : https://prove2.me/theorems/cd96e6a2-5e5e-4de7-be73-b73f1b373de1
-- title:
--   Eden: to Matrix fderiv planar Vector Field
-- statement:
--   The standard real two-dimensional Jacobian q(s)I+2q'(s)vv^T+Omega J, as the
--   matrix of the derivative, including the origin.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PlanarVectorField.lean#L51-L63
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PlanarVectorField.lean#L51-L63

import Definitions.Def_Eden_VectorFieldDerivative
import Definitions.Def_Eden_PlanarVectorField
set_option autoImplicit true
noncomputable section
open Eden

theorem Eden.toMatrix_fderiv_planarVectorField (Ω : ℝ) (p : PlanarSpace) :
    (fderiv ℝ (planarVectorField Ω) p).toLinearMap.toMatrix
      (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis =
      q (p 0 ^ 2 + p 1 ^ 2) • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
        (2 * deriv q (p 0 ^ 2 + p 1 ^ 2)) •
          Matrix.vecMulVec (fun i => p i) (fun i => p i) +
        Ω • !![0, -1; 1, 0] := by sorry
