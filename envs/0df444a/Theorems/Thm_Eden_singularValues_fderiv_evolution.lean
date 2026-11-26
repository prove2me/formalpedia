-- Prove2me | Theorems.Thm_Eden_singularValues_fderiv_evolution
-- name    : Eden.singularValues_fderiv_evolution
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:17:47.55422+00:00
-- url     : https://prove2.me/theorems/889d55aa-ef16-55bf-81b6-0eb5bb5228b2
-- title:
--   Eden: singular Values fderiv evolution
-- statement:
--   The complete multiset of ambient Euclidean singular values of the evolution
--   derivative, including their multiplicities and all zero-radius cases.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/SingularValues.lean#L93-L104
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/SingularValues.lean#L93-L104

import Definitions.Def_Eden_DerivativeDecomposition
import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Definitions.Def_Eden_SingularValues
set_option autoImplicit true
noncomputable section
open Polynomial
open Eden

theorem Eden.singularValues_fderiv_evolution (c : ℝ) {t : ℝ} (ht : 0 ≤ t) (p : PhaseSpace) :
    Finset.univ.val.map (fun i : Fin 5 => (fderiv ℝ (evolution c t) p).toLinearMap.singularValues i) =
      Finset.univ.val.map (fun i : Fin 5 => derivativeFactors c t p i) := by sorry
