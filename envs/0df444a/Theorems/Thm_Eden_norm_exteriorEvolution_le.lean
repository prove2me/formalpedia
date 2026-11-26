-- Prove2me | Theorems.Thm_Eden_norm_exteriorEvolution_le
-- name    : Eden.norm_exteriorEvolution_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:35:24.870963+00:00
-- url     : https://prove2.me/theorems/1991a873-5ae3-5923-95f6-f5fd6146139a
-- title:
--   Eden: norm exterior Evolution le
-- statement:
--   The Eden construction uses the norm exterior Evolution le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ExteriorOperatorNorm.lean#L81-L105
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ExteriorOperatorNorm.lean#L81-L105

import Definitions.Def_Eden_ExteriorMaximalGrowth
import Definitions.Def_Eden_SelectedProducts
import Definitions.Def_Eden_SingularValueFunction
import Definitions.Def_Eden_ExteriorOperatorNorm
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.norm_exteriorEvolution_le {k : ℕ} (hk : k ≤ 5) (c : ℝ) {t : ℝ}
    (ht : 0 ≤ t) (p : PhaseSpace) (v : ExteriorSpace k) :
    ‖exteriorEvolution k c t p v‖ ≤
      singularValueFunction (fderiv ℝ (evolution c t) p).toLinearMap k * ‖v‖ := by sorry
