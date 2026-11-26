-- Prove2me | Theorems.Thm_Eden_isGreatest_selectedSingularProduct
-- name    : Eden.isGreatest_selectedSingularProduct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:36:01.576263+00:00
-- url     : https://prove2.me/theorems/176bf5ab-303a-40e9-84b4-1e471d1e644f
-- title:
--   Eden: is Greatest selected Singular Product
-- statement:
--   The Eden construction uses the is Greatest selected Singular Product property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ExteriorSingularValues.lean#L15-L30
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ExteriorSingularValues.lean#L15-L30

import Definitions.Def_Eden_ExteriorGram
import Definitions.Def_Eden_ExteriorSingularValues
set_option autoImplicit true
noncomputable section
open Eden

theorem Eden.isGreatest_selectedSingularProduct {k : ℕ} (hk : k ≤ 5)
    (A : PhaseSpace →ₗ[ℝ] PhaseSpace) :
    IsGreatest (Set.range (selectedSingularProduct k A)) (singularValueFunction A k) := by sorry
