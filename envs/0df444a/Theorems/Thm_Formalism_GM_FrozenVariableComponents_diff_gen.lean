-- Prove2me | Theorems.Thm_Formalism_GM_FrozenVariableComponents_diff_gen
-- name    : Formalism.GM.FrozenVariableComponents.diff_gen
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:14:04.76179+00:00
-- url     : https://prove2.me/theorems/43aa66ed-c0bc-412c-8c8f-fa21f47cfc0d
-- title:
--   Frozen Variable Components: diff gen
-- statement:
--   The Frozen Variable Components construction uses the diff gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeY.lean#L647-L657
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeY.lean#L647-L657

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

theorem Formalism.GM.FrozenVariableComponents.diff_gen (LL : Letters N) (ρ c : Fin r) (hc : c ≠ ρ) (x : Fin N × Fin r) :
    X (Fin.last N, ρ) * pderiv (Fin.last N, c) (freezeSub p LL ρ x) =
      aeval (freezeSub p LL ρ) (glAct p LL N c ρ (X x)) := by sorry
