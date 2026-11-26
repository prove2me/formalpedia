-- Prove2me | Theorems.Thm_Eden_singularValues_fderiv_frequencyEvolution
-- name    : Eden.singularValues_fderiv_frequencyEvolution
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:16:54.16253+00:00
-- url     : https://prove2.me/theorems/2751d5b3-fd59-5d5c-b9db-2d23f5ce433c
-- title:
--   Eden: singular Values fderiv frequency Evolution
-- statement:
--   Full five-value multiset identity, including zero radii and time zero.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/FrequencySingularValues.lean#L26-L33
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/FrequencySingularValues.lean#L26-L33

import Definitions.Def_Eden_FrequencyRotation
import Definitions.Def_Eden_OrderedStationarySpectrum
import Definitions.Def_Eden_FrequencySingularValues
set_option autoImplicit true
noncomputable section
open Eden

theorem Eden.singularValues_fderiv_frequencyEvolution (c ν : ℝ) {t : ℝ} (ht : 0 ≤ t)
    (p : PhaseSpace) :
    Finset.univ.val.map (fun i : Fin 5 =>
      (fderiv ℝ (frequencyEvolution c ν t) p).toLinearMap.singularValues i) =
      Finset.univ.val.map (fun i : Fin 5 => derivativeFactors c t p i) := by sorry
