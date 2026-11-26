-- Prove2me | Theorems.Thm_Eden_tendsto_spectrumInterpolation_normalized
-- name    : Eden.tendsto_spectrumInterpolation_normalized
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:54:05.885493+00:00
-- url     : https://prove2.me/theorems/ed0f016f-b8b6-4921-a8f2-ed49d8da05ee
-- title:
--   Eden: tendsto spectrum Interpolation normalized
-- statement:
--   The Eden construction uses the tendsto spectrum Interpolation normalized property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/DimensionConvergenceCriteria.lean#L16-L20
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/DimensionConvergenceCriteria.lean#L16-L20

import Definitions.Def_Eden_FiniteTimeKaplanYorke
import Definitions.Def_Eden_DimensionConvergenceCriteria
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden

theorem Eden.tendsto_spectrumInterpolation_normalized (c : ℝ) (p : PhaseSpace) (d : ℝ) :
    Tendsto (fun t => spectrumInterpolation (normalizedLogSingularValues c t p) d)
      atTop (𝓝 (spectrumInterpolation (lyapunovExponent c p) d)) := by sorry
