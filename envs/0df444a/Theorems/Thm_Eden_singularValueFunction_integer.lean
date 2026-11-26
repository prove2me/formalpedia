-- Prove2me | Theorems.Thm_Eden_singularValueFunction_integer
-- name    : Eden.singularValueFunction_integer
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:34:57.463348+00:00
-- url     : https://prove2.me/theorems/17b3beb6-8943-4db1-b731-5791395d3de0
-- title:
--   Eden: singular Value Function integer
-- statement:
--   The Eden construction uses the singular Value Function integer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ExteriorOperatorNorm.lean#L28-L33
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ExteriorOperatorNorm.lean#L28-L33

import Definitions.Def_Eden_ExteriorMaximalGrowth
import Definitions.Def_Eden_SelectedProducts
import Definitions.Def_Eden_SingularValueFunction
import Definitions.Def_Eden_ExteriorOperatorNorm
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.singularValueFunction_integer (A : PhaseSpace →ₗ[ℝ] PhaseSpace)
    {k : ℕ} (hk : k ≤ 5) :
    singularValueFunction A k = ∏ i ∈ Finset.range k, A.singularValues i := by sorry
