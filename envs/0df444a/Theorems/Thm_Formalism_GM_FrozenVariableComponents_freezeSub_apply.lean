-- Prove2me | Theorems.Thm_Formalism_GM_FrozenVariableComponents_freezeSub_apply
-- name    : Formalism.GM.FrozenVariableComponents.freezeSub_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:21:08.818919+00:00
-- url     : https://prove2.me/theorems/a4fffcb0-8f80-4ba8-b95b-ecb9fad2e585
-- title:
--   Frozen Variable Components: freeze Sub apply
-- statement:
--   The Frozen Variable Components construction uses the freeze Sub apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeY.lean#L638-L645
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeY.lean#L638-L645

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

theorem Formalism.GM.FrozenVariableComponents.freezeSub_apply (LL : Letters N) (ρ : Fin r) (i : Fin N) (c : Fin r) :
    freezeSub p LL ρ (i, c) =
    if LL.vec i then
      (if c = ρ then ∑ c', X (Fin.castSucc i, c') * X (Fin.last N, c')
       else X (Fin.last N, ρ) * X (Fin.castSucc i, c))
    else
      (if c = ρ then X (Fin.last N, ρ) * X (Fin.castSucc i, ρ)
       else X (Fin.last N, ρ) * X (Fin.castSucc i, c) - X (Fin.castSucc i, ρ) * X (Fin.last N, c)) := by sorry
