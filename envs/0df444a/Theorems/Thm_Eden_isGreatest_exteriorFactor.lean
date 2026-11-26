-- Prove2me | Theorems.Thm_Eden_isGreatest_exteriorFactor
-- name    : Eden.isGreatest_exteriorFactor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:34:03.094175+00:00
-- url     : https://prove2.me/theorems/800ab4ba-7c85-4430-9aad-aaedc5f4555b
-- title:
--   Eden: is Greatest exterior Factor
-- statement:
--   The Eden construction uses the is Greatest exterior Factor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ExteriorOperatorNorm.lean#L48-L64
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ExteriorOperatorNorm.lean#L48-L64

import Definitions.Def_Eden_ExteriorMaximalGrowth
import Definitions.Def_Eden_SelectedProducts
import Definitions.Def_Eden_SingularValueFunction
import Definitions.Def_Eden_ExteriorOperatorNorm
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.isGreatest_exteriorFactor {k : ℕ} (hk : k ≤ 5) (c : ℝ) {t : ℝ}
    (ht : 0 ≤ t) (p : PhaseSpace) :
    IsGreatest (Set.range (exteriorFactor k (derivativeFactors c t p)))
      (singularValueFunction (fderiv ℝ (evolution c t) p).toLinearMap k) := by sorry
