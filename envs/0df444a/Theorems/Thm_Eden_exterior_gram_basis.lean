-- Prove2me | Theorems.Thm_Eden_exterior_gram_basis
-- name    : Eden.exterior_gram_basis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:35:44.557651+00:00
-- url     : https://prove2.me/theorems/48883f54-af7b-55ac-8124-5d8e87cf25b8
-- title:
--   Eden: exterior gram basis
-- statement:
--   The Eden construction uses the exterior gram basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ExteriorGram.lean#L80-L92
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ExteriorGram.lean#L80-L92

import Definitions.Def_Eden_ExteriorOperatorNorm
import Definitions.Def_Eden_ExteriorGram
set_option autoImplicit true
noncomputable section
open scoped RealInnerProductSpace
open Eden

theorem Eden.exterior_gram_basis (k : ℕ) (A : PhaseSpace →ₗ[ℝ] PhaseSpace)
    (s : ExteriorIndex k) :
    exteriorPower.map k (A.adjoint ∘ₗ A) (singularExteriorBasis k A s) =
      selectedSingularProduct k A s ^ 2 • singularExteriorBasis k A s := by sorry
