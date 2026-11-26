-- Prove2me | Theorems.Thm_Eden_exteriorOperator_apply
-- name    : Eden.exteriorOperator_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:34:48.092237+00:00
-- url     : https://prove2.me/theorems/aab7d51b-6b97-450b-a54a-afc44e6b38b4
-- title:
--   Eden: exterior Operator apply
-- statement:
--   The Eden construction uses the exterior Operator apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ExteriorOperatorNorm.lean#L25-L26
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ExteriorOperatorNorm.lean#L25-L26

import Definitions.Def_Eden_ExteriorMaximalGrowth
import Definitions.Def_Eden_SelectedProducts
import Definitions.Def_Eden_SingularValueFunction
import Definitions.Def_Eden_ExteriorOperatorNorm
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.exteriorOperator_apply (k : ℕ) (A : PhaseSpace →ₗ[ℝ] PhaseSpace)
    (v : ExteriorSpace k) : exteriorOperator k A v = exteriorPower.map k A v := by sorry
