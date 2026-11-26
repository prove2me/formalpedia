-- Prove2me | Theorems.Thm_Eden_hasDerivAt_frequencyEvolution
-- name    : Eden.hasDerivAt_frequencyEvolution
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:24:10.025872+00:00
-- url     : https://prove2.me/theorems/58083133-36d5-5b9d-a08c-6c5714d9b07f
-- title:
--   Eden: has Deriv At frequency Evolution
-- statement:
--   The time derivative is the new field, including at time zero.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/FrequencyEvolution.lean#L37-L52
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/FrequencyEvolution.lean#L37-L52

import Definitions.Def_Eden_Evolution
import Definitions.Def_Eden_InvariantSets
import Definitions.Def_Eden_FrequencyEvolution
set_option autoImplicit true
noncomputable section
open Eden

theorem Eden.hasDerivAt_frequencyEvolution (c ν : ℝ) {t : ℝ} (ht : 0 ≤ t) (p : PhaseSpace) :
    HasDerivAt (fun τ => frequencyEvolution c ν τ p)
      (frequencyVectorField c ν (frequencyEvolution c ν t p)) t := by sorry
