-- Prove2me | Theorems.Thm_Eden_fderiv_frequencyEvolution_orthogonal
-- name    : Eden.fderiv_frequencyEvolution_orthogonal
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:16:56.312826+00:00
-- url     : https://prove2.me/theorems/02947536-e244-48af-aa02-a13df9bce259
-- title:
--   Eden: fderiv frequency Evolution orthogonal
-- statement:
--   The Eden construction uses the fderiv frequency Evolution orthogonal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/FrequencySingularValues.lean#L15-L23
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/FrequencySingularValues.lean#L15-L23

import Definitions.Def_Eden_FrequencyRotation
import Definitions.Def_Eden_OrderedStationarySpectrum
import Definitions.Def_Eden_FrequencySingularValues
set_option autoImplicit true
noncomputable section
open Eden

theorem Eden.fderiv_frequencyEvolution_orthogonal (c ν : ℝ) {t : ℝ} (ht : 0 ≤ t)
    (p : PhaseSpace) :
    (fderiv ℝ (frequencyEvolution c ν t) p).toLinearMap =
      orthogonalDiagonalMap (((radialFrame p).trans (angularRotation t)).trans
        (frequencyCorrection ν t)) (radialFrame p) (derivativeFactors c t p) := by sorry
