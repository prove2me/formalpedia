-- Prove2me | Theorems.Thm_Eden_norm_exteriorEvolution_initialBasis
-- name    : Eden.norm_exteriorEvolution_initialBasis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:35:15.790578+00:00
-- url     : https://prove2.me/theorems/a6ad9e0a-fa8c-4bb6-8942-c7e7d2dfc294
-- title:
--   Eden: norm exterior Evolution initial Basis
-- statement:
--   The Eden construction uses the norm exterior Evolution initial Basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ExteriorOperatorNorm.lean#L71-L79
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ExteriorOperatorNorm.lean#L71-L79

import Definitions.Def_Eden_ExteriorMaximalGrowth
import Definitions.Def_Eden_SelectedProducts
import Definitions.Def_Eden_SingularValueFunction
import Definitions.Def_Eden_ExteriorOperatorNorm
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.norm_exteriorEvolution_initialBasis (k : ℕ) (c : ℝ) {t : ℝ}
    (ht : 0 ≤ t) (p : PhaseSpace) (s : ExteriorIndex k) :
    ‖exteriorEvolution k c t p (initialExteriorBasisVector k p s)‖ =
      exteriorFactor k (derivativeFactors c t p) s := by sorry
