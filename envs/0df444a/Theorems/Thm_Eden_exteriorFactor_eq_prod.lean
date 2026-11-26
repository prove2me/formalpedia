-- Prove2me | Theorems.Thm_Eden_exteriorFactor_eq_prod
-- name    : Eden.exteriorFactor_eq_prod
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:34:04.544682+00:00
-- url     : https://prove2.me/theorems/a8ff8743-bd0b-4fd2-b4de-7bba947f3d6e
-- title:
--   Eden: exterior Factor eq prod
-- statement:
--   The Eden construction uses the exterior Factor eq prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ExteriorOperatorNorm.lean#L41-L46
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ExteriorOperatorNorm.lean#L41-L46

import Definitions.Def_Eden_ExteriorMaximalGrowth
import Definitions.Def_Eden_SelectedProducts
import Definitions.Def_Eden_SingularValueFunction
import Definitions.Def_Eden_ExteriorOperatorNorm
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.exteriorFactor_eq_prod (k : ℕ) (d : PhaseSpace) (s : ExteriorIndex k) :
    exteriorFactor k d s = ∏ j ∈ s.val, d j := by sorry
