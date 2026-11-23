-- Prove2me | Theorems.Thm_Formalism_GM_FrozenVariableComponents_wt_snoc
-- name    : Formalism.GM.FrozenVariableComponents.wt_snoc
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:42:38.246869+00:00
-- url     : https://prove2.me/theorems/532151b6-dd00-4d74-a7e1-ddae471f098e
-- title:
--   Frozen Variable Components: wt snoc
-- statement:
--   The Frozen Variable Components construction uses the wt snoc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeY.lean#L280-L285
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeY.lean#L280-L285

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

theorem Formalism.GM.FrozenVariableComponents.wt_snoc (LL : Letters N) (n j : ℕ) (hj : j ≤ N) (c : Fin r) (m : Fin (N + 1) × Fin r →₀ ℕ) :
    wt (LL.snoc n) j c m = wt LL j c (llPart m) := by sorry
