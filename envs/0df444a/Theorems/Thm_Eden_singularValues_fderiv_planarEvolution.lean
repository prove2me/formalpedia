-- Prove2me | Theorems.Thm_Eden_singularValues_fderiv_planarEvolution
-- name    : Eden.singularValues_fderiv_planarEvolution
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:01:34.927237+00:00
-- url     : https://prove2.me/theorems/8d244a9d-4b20-49be-bd35-7bd677d0381a
-- title:
--   Eden: singular Values fderiv planar Evolution
-- statement:
--   Both standard Mathlib singular values of the planar derivative, as a multiset,
--   for every real frequency and every initial point, including zero radius and time
--   zero.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PlanarSingularValues.lean#L74-L96
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PlanarSingularValues.lean#L74-L96

import Definitions.Def_Eden_PlanarDerivative
import Definitions.Def_Eden_StationaryFactors
import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Definitions.Def_Eden_PlanarSingularValues
set_option autoImplicit true
noncomputable section
open Polynomial
open Eden

theorem Eden.singularValues_fderiv_planarEvolution (Ω : ℝ) {t : ℝ} (ht : 0 ≤ t)
    (p : PlanarSpace) :
    Finset.univ.val.map (fun i : Fin 2 =>
      (fderiv ℝ (planarEvolution Ω t) p).toLinearMap.singularValues i) =
      Finset.univ.val.map (fun i : Fin 2 => planarFactors t p i) := by sorry
