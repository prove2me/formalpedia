-- Prove2me | Theorems.Thm_Eden_ordered_singularValues_frequencyEvolution
-- name    : Eden.ordered_singularValues_frequencyEvolution
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:17:41.929374+00:00
-- url     : https://prove2.me/theorems/684c07bb-b4c6-5cdf-a0e1-557b55ee796f
-- title:
--   Eden: ordered singular Values frequency Evolution
-- statement:
--   The Eden construction uses the ordered singular Values frequency Evolution property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/FrequencySingularValues.lean#L35-L43
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/FrequencySingularValues.lean#L35-L43

import Definitions.Def_Eden_FrequencyRotation
import Definitions.Def_Eden_OrderedStationarySpectrum
import Definitions.Def_Eden_FrequencySingularValues
set_option autoImplicit true
noncomputable section
open Eden

theorem Eden.ordered_singularValues_frequencyEvolution (c ν : ℝ) {t : ℝ} (ht : 0 ≤ t)
    (p : PhaseSpace) :
    (fun i : Fin 5 => (fderiv ℝ (frequencyEvolution c ν t) p).toLinearMap.singularValues i) =
      fun i : Fin 5 => (fderiv ℝ (evolution c t) p).toLinearMap.singularValues i := by sorry
