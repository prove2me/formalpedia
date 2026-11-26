-- Prove2me | Theorems.Thm_Eden_fderiv_planarEvolution_orthogonal_decomposition
-- name    : Eden.fderiv_planarEvolution_orthogonal_decomposition
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:01:23.797393+00:00
-- url     : https://prove2.me/theorems/1ed65e35-1586-4e85-9ddc-bd86696476ed
-- title:
--   Eden: fderiv planar Evolution orthogonal decomposition
-- statement:
--   Orthogonal factorisation of the derivative at every planar point, with no
--   restrictions on the real angular frequency.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PlanarSingularValues.lean#L51-L58
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PlanarSingularValues.lean#L51-L58

import Definitions.Def_Eden_PlanarDerivative
import Definitions.Def_Eden_StationaryFactors
import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Definitions.Def_Eden_PlanarSingularValues
set_option autoImplicit true
noncomputable section
open Polynomial
open Eden

theorem Eden.fderiv_planarEvolution_orthogonal_decomposition (Ω : ℝ) {t : ℝ}
    (ht : 0 ≤ t) (p : PlanarSpace) :
    (fderiv ℝ (planarEvolution Ω t) p).toLinearMap =
      ((planarRadialFrame p).trans (planarAngularRotation Ω t)).toLinearMap ∘ₗ
        planarDiagonal (planarFactors t p) ∘ₗ (planarRadialFrame p).symm.toLinearMap := by sorry
