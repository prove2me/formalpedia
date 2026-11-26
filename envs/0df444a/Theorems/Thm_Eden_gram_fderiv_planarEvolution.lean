-- Prove2me | Theorems.Thm_Eden_gram_fderiv_planarEvolution
-- name    : Eden.gram_fderiv_planarEvolution
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:01:25.661929+00:00
-- url     : https://prove2.me/theorems/b6ebb7b3-4376-4540-b535-310cef92b028
-- title:
--   Eden: gram fderiv planar Evolution
-- statement:
--   The Eden construction uses the gram fderiv planar Evolution property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PlanarSingularValues.lean#L60-L69
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PlanarSingularValues.lean#L60-L69

import Definitions.Def_Eden_PlanarDerivative
import Definitions.Def_Eden_StationaryFactors
import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Definitions.Def_Eden_PlanarSingularValues
set_option autoImplicit true
noncomputable section
open Polynomial
open Eden

theorem Eden.gram_fderiv_planarEvolution (Ω : ℝ) {t : ℝ} (ht : 0 ≤ t) (p : PlanarSpace) :
    (fderiv ℝ (planarEvolution Ω t) p).toLinearMap.adjoint ∘ₗ
        (fderiv ℝ (planarEvolution Ω t) p).toLinearMap =
      (planarRadialFrame p).toLinearEquiv.conj
        (planarDiagonal (WithLp.toLp 2 (fun i => planarFactors t p i ^ 2))) := by sorry
