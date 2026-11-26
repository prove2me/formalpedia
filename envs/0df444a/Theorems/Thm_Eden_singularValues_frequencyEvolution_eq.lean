-- Prove2me | Theorems.Thm_Eden_singularValues_frequencyEvolution_eq
-- name    : Eden.singularValues_frequencyEvolution_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:20:05.35598+00:00
-- url     : https://prove2.me/theorems/bc7ce0a0-2f9b-5f99-a719-f1d1067a3b4d
-- title:
--   Eden: singular Values frequency Evolution eq
-- statement:
--   Equality of the singular-value sequences, including their zero tails.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/FrequencySingularValues.lean#L46-L54
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/FrequencySingularValues.lean#L46-L54

import Definitions.Def_Eden_FrequencyRotation
import Definitions.Def_Eden_OrderedStationarySpectrum
import Definitions.Def_Eden_FrequencySingularValues
set_option autoImplicit true
noncomputable section
open Eden

theorem Eden.singularValues_frequencyEvolution_eq (c ν : ℝ) {t : ℝ} (ht : 0 ≤ t)
    (p : PhaseSpace) :
    (fderiv ℝ (frequencyEvolution c ν t) p).toLinearMap.singularValues =
      (fderiv ℝ (evolution c t) p).toLinearMap.singularValues := by sorry
