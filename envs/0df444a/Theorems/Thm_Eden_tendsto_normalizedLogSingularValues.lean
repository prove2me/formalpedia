-- Prove2me | Theorems.Thm_Eden_tendsto_normalizedLogSingularValues
-- name    : Eden.tendsto_normalizedLogSingularValues
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:44:24.331873+00:00
-- url     : https://prove2.me/theorems/190e62c5-750e-40a0-ab9b-6b452914256d
-- title:
--   Eden: tendsto normalized Log Singular Values
-- statement:
--   The Eden construction uses the tendsto normalized Log Singular Values property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/LyapunovExponents.lean#L53-L58
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/LyapunovExponents.lean#L53-L58

import Definitions.Def_Eden_FactorLimits
import Definitions.Def_Eden_Sorting
import Definitions.Def_Eden_LyapunovExponents
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden

theorem Eden.tendsto_normalizedLogSingularValues (c : ℝ) (p : PhaseSpace) :
    Tendsto (fun t => normalizedLogSingularValues c t p) atTop
      (𝓝 (descending (factorExponents c p))) := by sorry
