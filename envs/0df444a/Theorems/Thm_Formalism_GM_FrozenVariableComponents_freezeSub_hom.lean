-- Prove2me | Theorems.Thm_Formalism_GM_FrozenVariableComponents_freezeSub_hom
-- name    : Formalism.GM.FrozenVariableComponents.freezeSub_hom
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:14:02.971802+00:00
-- url     : https://prove2.me/theorems/c30bc54f-618d-42ed-bf7d-f430dea8a3fc
-- title:
--   Frozen Variable Components: freeze Sub hom
-- statement:
--   The Frozen Variable Components construction uses the freeze Sub hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeY.lean#L970-L984
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeY.lean#L970-L984

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

theorem Formalism.GM.FrozenVariableComponents.freezeSub_hom (LL : Letters N) (ρ : Fin r) (i' : Fin (N + 1)) (x : Fin N × Fin r) :
    IsWeightedHomogeneous (fun y : Fin (N + 1) × Fin r => if y.1 = i' then 1 else 0) (freezeSub p LL ρ x)
      ((if Fin.castSucc x.1 = i' then 1 else 0) + (if Fin.last N = i' then 1 else 0)) := by sorry
