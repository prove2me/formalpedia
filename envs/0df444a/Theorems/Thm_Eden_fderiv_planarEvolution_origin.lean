-- Prove2me | Theorems.Thm_Eden_fderiv_planarEvolution_origin
-- name    : Eden.fderiv_planarEvolution_origin
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:30:41.784153+00:00
-- url     : https://prove2.me/theorems/f4c1d047-71d4-530e-8274-c287a5a4dda5
-- title:
--   Eden: fderiv planar Evolution origin
-- statement:
--   At the planar origin the derivative is the exponential contraction times the
--   angular rotation, for every real frequency.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PlanarSingularValues.lean#L124-L130
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PlanarSingularValues.lean#L124-L130

import Definitions.Def_Eden_PlanarDerivative
import Definitions.Def_Eden_StationaryFactors
import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Definitions.Def_Eden_PlanarSingularValues
set_option autoImplicit true
noncomputable section
open Polynomial
open Eden

theorem Eden.fderiv_planarEvolution_origin (Ω : ℝ) {t : ℝ} (ht : 0 ≤ t) (v : PlanarSpace) :
    fderiv ℝ (planarEvolution Ω t) 0 v =
      Real.exp (-2 * t) • planarAngularRotation Ω t v := by sorry
