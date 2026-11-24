-- Prove2me | Theorems.Thm_Formalism_GM_FrozenVariableComponents_ycond_full
-- name    : Formalism.GM.FrozenVariableComponents.ycond_full
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:14:31.863797+00:00
-- url     : https://prove2.me/theorems/aaaa85fe-af42-4f80-a4f5-2827ac65fd6c
-- title:
--   Frozen Variable Components: ycond full
-- statement:
--   The Frozen Variable Components construction uses the ycond full property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeY.lean#L576-L583
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeY.lean#L576-L583

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
variable [NeZero r]

theorem Formalism.GM.FrozenVariableComponents.ycond_full (LL : Letters N) (j : ℕ) (M : WithTop ℤ) (c d : Fin r)
    (F : MvPolynomial (Fin N × Fin r) ℚ_[p]) (hF : F ∈ YCond p LL j M) :
    glAct p LL N c d F ∈ YCond p LL j M := by sorry
