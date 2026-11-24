-- Prove2me | Theorems.Thm_Formalism_GM_FrozenVariableComponents_kill_freezeSub
-- name    : Formalism.GM.FrozenVariableComponents.kill_freezeSub
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:14:17.020387+00:00
-- url     : https://prove2.me/theorems/fb733e8f-c83a-4d13-a798-caf9784f559f
-- title:
--   Frozen Variable Components: kill freeze Sub
-- statement:
--   The Frozen Variable Components construction uses the kill freeze Sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeY.lean#L734-L743
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeY.lean#L734-L743

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

theorem Formalism.GM.FrozenVariableComponents.kill_freezeSub (LL : Letters N) (ρ : Fin r) :
    (kill p ρ).comp (aeval (freezeSub p LL ρ)) =
      aeval (fun x : Fin N × Fin r =>
        (X (Fin.last N, ρ) * X (emb x) : MvPolynomial (Fin (N + 1) × Fin r) ℚ_[p])) := by sorry
