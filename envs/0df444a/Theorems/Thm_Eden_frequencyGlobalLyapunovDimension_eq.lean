-- Prove2me | Theorems.Thm_Eden_frequencyGlobalLyapunovDimension_eq
-- name    : Eden.frequencyGlobalLyapunovDimension_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:21:59.914167+00:00
-- url     : https://prove2.me/theorems/0e7d5a2b-83ee-46a4-8a53-2dd053a311e6
-- title:
--   Eden: frequency Global Lyapunov Dimension eq
-- statement:
--   The Eden construction uses the frequency Global Lyapunov Dimension eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/FrequencyDimensions.lean#L35-L42
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/FrequencyDimensions.lean#L35-L42

import Definitions.Def_Eden_FrequencySingularValues
import Definitions.Def_Eden_DimensionConvergence
import Definitions.Def_Eden_FrequencyDimensions
set_option autoImplicit true
noncomputable section
open Set Filter Topology
open Eden

theorem Eden.frequencyGlobalLyapunovDimension_eq (c ν : ℝ) (K : Set PhaseSpace) :
    frequencyGlobalLyapunovDimension c ν K = globalLyapunovDimension c K := by sorry
