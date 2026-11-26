-- Prove2me | Theorems.Thm_Eden_exteriorOperator_comp
-- name    : Eden.exteriorOperator_comp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:37:11.803744+00:00
-- url     : https://prove2.me/theorems/32450744-be99-4b3c-86bc-a2a7c3a87e1e
-- title:
--   Eden: exterior Operator comp
-- statement:
--   The Eden construction uses the exterior Operator comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ExteriorCocycle.lean#L16-L21
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ExteriorCocycle.lean#L16-L21

import Definitions.Def_Eden_ExteriorSingularValues
import Definitions.Def_Eden_Uniqueness
import Definitions.Def_Eden_ExteriorCocycle
set_option autoImplicit true
noncomputable section
open Eden

theorem Eden.exteriorOperator_comp (k : ℕ) (A B : PhaseSpace →ₗ[ℝ] PhaseSpace) :
    exteriorOperator k (A ∘ₗ B) = (exteriorOperator k A).comp (exteriorOperator k B) := by sorry
