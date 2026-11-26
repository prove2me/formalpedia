-- Prove2me | Theorems.Thm_Eden_fderiv_frequencyEvolution_bijective
-- name    : Eden.fderiv_frequencyEvolution_bijective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:56:12.004625+00:00
-- url     : https://prove2.me/theorems/0f6e8023-9806-5c4f-bc94-57b022170f93
-- title:
--   Eden: fderiv frequency Evolution bijective
-- statement:
--   The Eden construction uses the fderiv frequency Evolution bijective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/FrequencySingularValues.lean#L56-L59
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/FrequencySingularValues.lean#L56-L59

import Definitions.Def_Eden_FrequencyRotation
import Definitions.Def_Eden_OrderedStationarySpectrum
import Definitions.Def_Eden_FrequencySingularValues
set_option autoImplicit true
noncomputable section
open Eden

theorem Eden.fderiv_frequencyEvolution_bijective (c ν : ℝ) {t : ℝ} (ht : 0 ≤ t)
    (p : PhaseSpace) : Function.Bijective (fderiv ℝ (frequencyEvolution c ν t) p) := by sorry
