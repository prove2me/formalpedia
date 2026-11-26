-- Prove2me | Theorems.Thm_Eden_selectedSingularProduct_eq_prod
-- name    : Eden.selectedSingularProduct_eq_prod
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:35:38.356174+00:00
-- url     : https://prove2.me/theorems/30d8dc49-b2ff-5ec4-be8e-7dd0d0a6c45b
-- title:
--   Eden: selected Singular Product eq prod
-- statement:
--   The Eden construction uses the selected Singular Product eq prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ExteriorGram.lean#L69-L72
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ExteriorGram.lean#L69-L72

import Definitions.Def_Eden_ExteriorOperatorNorm
import Definitions.Def_Eden_ExteriorGram
set_option autoImplicit true
noncomputable section
open scoped RealInnerProductSpace
open Eden

theorem Eden.selectedSingularProduct_eq_prod (k : ℕ) (A : PhaseSpace →ₗ[ℝ] PhaseSpace)
    (s : ExteriorIndex k) : selectedSingularProduct k A s = ∏ j ∈ s.val, A.singularValues j := by sorry
