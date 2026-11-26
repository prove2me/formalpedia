-- Prove2me | Theorems.Thm_Eden_finiteTimeDimension_ge_one_of_tangential_factor
-- name    : Eden.finiteTimeDimension_ge_one_of_tangential_factor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:54:44.042896+00:00
-- url     : https://prove2.me/theorems/93d8cb10-db48-5077-999c-306bb9d138aa
-- title:
--   Eden: finite Time Dimension ge one of tangential factor
-- statement:
--   The Eden construction uses the finite Time Dimension ge one of tangential factor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/NeutralDimensionBounds.lean#L54-L67
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/NeutralDimensionBounds.lean#L54-L67

import Definitions.Def_Eden_FiniteTimeKaplanYorke
import Definitions.Def_Eden_FactorBounds
import Definitions.Def_Eden_NeutralDimensionBounds
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.finiteTimeDimension_ge_one_of_tangential_factor (c : ℝ) {t : ℝ} (ht : 0 < t)
    (p : PhaseSpace) (i : Fin 5) (hi : 0 ≤ Real.log (derivativeFactors c t p i)) :
    1 ≤ finiteTimeDimension c t p := by sorry
