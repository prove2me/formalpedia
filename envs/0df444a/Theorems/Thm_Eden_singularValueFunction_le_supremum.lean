-- Prove2me | Theorems.Thm_Eden_singularValueFunction_le_supremum
-- name    : Eden.singularValueFunction_le_supremum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:38:45.340189+00:00
-- url     : https://prove2.me/theorems/38ef5b5e-899a-43e3-bd01-d21028847821
-- title:
--   Eden: singular Value Function le supremum
-- statement:
--   The Eden construction uses the singular Value Function le supremum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/GlobalGrowth.lean#L52-L55
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/GlobalGrowth.lean#L52-L55

import Definitions.Def_Eden_IntegerGrowthBounds
import Definitions.Def_Eden_GlobalGrowth
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.singularValueFunction_le_supremum {k : ℕ} (hk : k ≤ 5) {c t : ℝ}
    (hc : 4 ≤ c) (ht : 0 ≤ t) {p : PhaseSpace} (hp : p ∈ attractor) :
    singularValueFunction (fderiv ℝ (evolution c t) p).toLinearMap k ≤ supremumSingularProduct c k t := by sorry
