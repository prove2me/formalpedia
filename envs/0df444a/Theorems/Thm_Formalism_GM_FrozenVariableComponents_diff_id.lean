-- Prove2me | Theorems.Thm_Formalism_GM_FrozenVariableComponents_diff_id
-- name    : Formalism.GM.FrozenVariableComponents.diff_id
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:14:03.74513+00:00
-- url     : https://prove2.me/theorems/fb5e904a-2a38-47a9-9e1a-2719b90dfc92
-- title:
--   Frozen Variable Components: diff id
-- statement:
--   The Frozen Variable Components construction uses the diff id property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeY.lean#L659-L673
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeY.lean#L659-L673

import Definitions.Def_Formalism_MahlerMeasure_IsFrozenInv
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeY
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.FrozenVariableComponents
open MvPolynomial Finset Formalism.GM.M
variable (p : ℕ) [Fact p.Prime] {N r : ℕ}

theorem Formalism.GM.FrozenVariableComponents.diff_id (LL : Letters N) (ρ c : Fin r) (hc : c ≠ ρ) (f : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    X (Fin.last N, ρ) * pderiv (Fin.last N, c) (aeval (freezeSub p LL ρ) f) =
      aeval (freezeSub p LL ρ) (glAct p LL N c ρ f) := by sorry
