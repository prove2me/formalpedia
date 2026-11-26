-- Prove2me | Theorems.Thm_Eden_tendsto_spectrumPartialSum_normalized
-- name    : Eden.tendsto_spectrumPartialSum_normalized
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:59:40.802829+00:00
-- url     : https://prove2.me/theorems/8ae64ce6-4aa9-4862-8ffb-afaa6ef19975
-- title:
--   Eden: tendsto spectrum Partial Sum normalized
-- statement:
--   The Eden construction uses the tendsto spectrum Partial Sum normalized property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/EventualDimensionFormulas.lean#L38-L47
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/EventualDimensionFormulas.lean#L38-L47

import Definitions.Def_Eden_DimensionConvergence
import Definitions.Def_Eden_EventualDimensionFormulas
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden

theorem Eden.tendsto_spectrumPartialSum_normalized (c : ℝ) (p : PhaseSpace) (k : ℕ) :
    Tendsto (fun t => spectrumPartialSum (normalizedLogSingularValues c t p) k)
      atTop (𝓝 (spectrumPartialSum (lyapunovExponent c p) k)) := by sorry
