-- Prove2me | Theorems.Thm_Eden_singularValues_fderiv_planarEvolution_integrals
-- name    : Eden.singularValues_fderiv_planarEvolution_integrals
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:30:41.182733+00:00
-- url     : https://prove2.me/theorems/70c516b6-0fca-44fd-8bd9-7a7d9143efba
-- title:
--   Eden: singular Values fderiv planar Evolution integrals
-- statement:
--   The manuscript's planar singular-value formula as the two exponential integrals
--   along the planar trajectory, with full multiplicities.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PlanarSingularValues.lean#L100-L120
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PlanarSingularValues.lean#L100-L120

import Definitions.Def_Eden_PlanarDerivative
import Definitions.Def_Eden_StationaryFactors
import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Definitions.Def_Eden_PlanarSingularValues
set_option autoImplicit true
noncomputable section
open Polynomial
open Eden

theorem Eden.singularValues_fderiv_planarEvolution_integrals (Ω : ℝ) {t : ℝ} (ht : 0 ≤ t)
    (p : PlanarSpace) :
    Finset.univ.val.map (fun i : Fin 2 =>
      (fderiv ℝ (planarEvolution Ω t) p).toLinearMap.singularValues i) =
      {Real.exp (∫ τ in (0 : ℝ)..t, radialRate
          (planarEvolution Ω τ p 0 ^ 2 + planarEvolution Ω τ p 1 ^ 2)),
       Real.exp (∫ τ in (0 : ℝ)..t, tangentialRate
          (planarEvolution Ω τ p 0 ^ 2 + planarEvolution Ω τ p 1 ^ 2))} := by sorry
