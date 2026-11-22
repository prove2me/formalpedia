-- Prove2me | Theorems.Thm_Formalism_GM_FrozenVariableComponents_glAct_apply
-- name    : Formalism.GM.FrozenVariableComponents.glAct_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:32:40.780951+00:00
-- url     : https://prove2.me/theorems/2f184070-9c89-4c4f-af33-ee1e66737188
-- title:
--   Frozen Variable Components: gl Act apply
-- statement:
--   The Frozen Variable Components construction uses the gl Act apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeY.lean#L249-L255
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeY.lean#L249-L255

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

theorem Formalism.GM.FrozenVariableComponents.glAct_apply (LL : Letters N) (j : ℕ) (c d : Fin r) (F : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    glAct p LL j c d F = ∑ i : Fin N, if (i : ℕ) < j then
      (if LL.vec i then X (i, c) * pderiv (i, d) F else -(X (i, d) * pderiv (i, c) F)) else 0 := by sorry
