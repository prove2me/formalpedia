-- Prove2me | Theorems.Thm_Eden_normalizedLogSingularValues_eq_descending
-- name    : Eden.normalizedLogSingularValues_eq_descending
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:46:29.063895+00:00
-- url     : https://prove2.me/theorems/d9634140-1d7a-493d-935a-153221659e09
-- title:
--   Eden: normalized Log Singular Values eq descending
-- statement:
--   The Eden construction uses the normalized Log Singular Values eq descending property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/LyapunovExponents.lean#L38-L51
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/LyapunovExponents.lean#L38-L51

import Definitions.Def_Eden_FactorLimits
import Definitions.Def_Eden_Sorting
import Definitions.Def_Eden_LyapunovExponents
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden

theorem Eden.normalizedLogSingularValues_eq_descending (c : ℝ) {t : ℝ} (ht : 0 < t)
    (p : PhaseSpace) :
    normalizedLogSingularValues c t p =
      descending (fun i => Real.log (derivativeFactors c t p i) / t) := by sorry
