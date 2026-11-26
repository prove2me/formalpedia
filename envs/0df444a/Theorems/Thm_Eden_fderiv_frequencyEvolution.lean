-- Prove2me | Theorems.Thm_Eden_fderiv_frequencyEvolution
-- name    : Eden.fderiv_frequencyEvolution
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:16:14.438405+00:00
-- url     : https://prove2.me/theorems/d48ce1fc-c88f-5f03-a359-4511bca56d8d
-- title:
--   Eden: fderiv frequency Evolution
-- statement:
--   The ambient derivative differs only by an orthogonal output map.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/FrequencyRotation.lean#L84-L92
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/FrequencyRotation.lean#L84-L92

import Definitions.Def_Eden_FrequencyEvolution
import Definitions.Def_Eden_DerivativeDecomposition
import Definitions.Def_Eden_FrequencyRotation
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.fderiv_frequencyEvolution (c ν : ℝ) {t : ℝ} (ht : 0 ≤ t) (p : PhaseSpace) :
    fderiv ℝ (frequencyEvolution c ν t) p =
      (frequencyCorrection ν t).toContinuousLinearEquiv.toContinuousLinearMap.comp
        (fderiv ℝ (evolution c t) p) := by sorry
