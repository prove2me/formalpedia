-- Prove2me | Theorems.Thm_Eden_normalizedLogSingularValues_antitone
-- name    : Eden.normalizedLogSingularValues_antitone
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:45:22.930041+00:00
-- url     : https://prove2.me/theorems/193915af-27bd-583f-9bb0-7af92956631d
-- title:
--   Eden: normalized Log Singular Values antitone
-- statement:
--   The Eden construction uses the normalized Log Singular Values antitone property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/LyapunovExponents.lean#L31-L36
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/LyapunovExponents.lean#L31-L36

import Definitions.Def_Eden_FactorLimits
import Definitions.Def_Eden_Sorting
import Definitions.Def_Eden_LyapunovExponents
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden

theorem Eden.normalizedLogSingularValues_antitone (c : ℝ) {t : ℝ} (ht : 0 < t)
    (p : PhaseSpace) : Antitone (normalizedLogSingularValues c t p) := by sorry
