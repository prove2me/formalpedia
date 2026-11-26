-- Prove2me | Theorems.Thm_Eden_singularValueFunction_integer_eq_fin_prod
-- name    : Eden.singularValueFunction_integer_eq_fin_prod
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:33:38.035879+00:00
-- url     : https://prove2.me/theorems/72d48bb2-b710-5dc0-89a5-102e11d7da77
-- title:
--   Eden: singular Value Function integer eq fin prod
-- statement:
--   The Eden construction uses the singular Value Function integer eq fin prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ExteriorOperatorNorm.lean#L35-L39
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ExteriorOperatorNorm.lean#L35-L39

import Definitions.Def_Eden_ExteriorMaximalGrowth
import Definitions.Def_Eden_SelectedProducts
import Definitions.Def_Eden_SingularValueFunction
import Definitions.Def_Eden_ExteriorOperatorNorm
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.singularValueFunction_integer_eq_fin_prod (A : PhaseSpace →ₗ[ℝ] PhaseSpace)
    {k : ℕ} (hk : k ≤ 5) :
    singularValueFunction A k = ∏ i : Fin k, A.singularValues (Fin.castLE hk i) := by sorry
