-- Prove2me | Theorems.Thm_Eden_singularValueFunction_frequencyEvolution
-- name    : Eden.singularValueFunction_frequencyEvolution
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:21:43.754801+00:00
-- url     : https://prove2.me/theorems/cbdabc6a-80d4-5400-856f-2c35a60d7c8d
-- title:
--   Eden: singular Value Function frequency Evolution
-- statement:
--   The Eden construction uses the singular Value Function frequency Evolution property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/FrequencyDimensions.lean#L16-L20
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/FrequencyDimensions.lean#L16-L20

import Definitions.Def_Eden_FrequencySingularValues
import Definitions.Def_Eden_DimensionConvergence
import Definitions.Def_Eden_FrequencyDimensions
set_option autoImplicit true
noncomputable section
open Set Filter Topology
open Eden

theorem Eden.singularValueFunction_frequencyEvolution (c ν : ℝ) {t : ℝ} (ht : 0 ≤ t)
    (p : PhaseSpace) (d : ℝ) :
    singularValueFunction (fderiv ℝ (frequencyEvolution c ν t) p).toLinearMap d =
      singularValueFunction (fderiv ℝ (evolution c t) p).toLinearMap d := by sorry
