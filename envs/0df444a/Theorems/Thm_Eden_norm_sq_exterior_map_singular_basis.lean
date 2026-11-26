-- Prove2me | Theorems.Thm_Eden_norm_sq_exterior_map_singular_basis
-- name    : Eden.norm_sq_exterior_map_singular_basis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:35:07.029689+00:00
-- url     : https://prove2.me/theorems/8b9393f2-29e8-4980-8b17-7d8cff0bdade
-- title:
--   Eden: norm sq exterior map singular basis
-- statement:
--   Exact squared norm for all exterior vectors and every ambient linear map,
--   including maps of deficient rank and zero selected products.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ExteriorGram.lean#L96-L111
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ExteriorGram.lean#L96-L111

import Definitions.Def_Eden_ExteriorOperatorNorm
import Definitions.Def_Eden_ExteriorGram
set_option autoImplicit true
noncomputable section
open scoped RealInnerProductSpace
open Eden

theorem Eden.norm_sq_exterior_map_singular_basis (k : ℕ) (A : PhaseSpace →ₗ[ℝ] PhaseSpace)
    (v : ExteriorSpace k) :
    ‖exteriorPower.map k A v‖ ^ 2 = ∑ s : ExteriorIndex k,
      (selectedSingularProduct k A s * (singularExteriorBasis k A).repr v s) ^ 2 := by sorry
