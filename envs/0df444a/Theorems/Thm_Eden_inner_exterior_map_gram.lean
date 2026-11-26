-- Prove2me | Theorems.Thm_Eden_inner_exterior_map_gram
-- name    : Eden.inner_exterior_map_gram
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:35:30.758387+00:00
-- url     : https://prove2.me/theorems/6a63ac3c-f2f6-5858-a5fa-28c8549c8cc3
-- title:
--   Eden: inner exterior map gram
-- statement:
--   The Gram identity for the exterior map, without invertibility.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ExteriorGram.lean#L18-L40
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ExteriorGram.lean#L18-L40

import Definitions.Def_Eden_ExteriorOperatorNorm
import Definitions.Def_Eden_ExteriorGram
set_option autoImplicit true
noncomputable section
open scoped RealInnerProductSpace
open Eden

theorem Eden.inner_exterior_map_gram (k : ℕ) (A : PhaseSpace →ₗ[ℝ] PhaseSpace)
    (v w : ExteriorSpace k) :
    ⟪exteriorPower.map k A v, exteriorPower.map k A w⟫ =
      ⟪v, exteriorPower.map k (A.adjoint ∘ₗ A) w⟫ := by sorry
