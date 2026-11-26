-- Prove2me | Theorems.Thm_Eden_singularValues_evolution_pos
-- name    : Eden.singularValues_evolution_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:45:31.085522+00:00
-- url     : https://prove2.me/theorems/6a317f44-f147-4b46-a6c0-3fdd65bfbd01
-- title:
--   Eden: singular Values evolution pos
-- statement:
--   The Eden construction uses the singular Values evolution pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/LyapunovExponents.lean#L24-L29
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/LyapunovExponents.lean#L24-L29

import Definitions.Def_Eden_FactorLimits
import Definitions.Def_Eden_Sorting
import Definitions.Def_Eden_LyapunovExponents
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden

theorem Eden.singularValues_evolution_pos (c : ℝ) {t : ℝ} (ht : 0 ≤ t)
    (p : PhaseSpace) (i : Fin 5) :
    0 < (fderiv ℝ (evolution c t) p).toLinearMap.singularValues i := by sorry
