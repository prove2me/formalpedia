-- Prove2me | Theorems.Thm_Formalism_GM_FrozenVariableComponents_top_apply
-- name    : Formalism.GM.FrozenVariableComponents.top_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:33:19.507966+00:00
-- url     : https://prove2.me/theorems/27fdc4bf-9095-4e84-84e8-0e69b4a00789
-- title:
--   Frozen Variable Components: top apply
-- statement:
--   The Frozen Variable Components construction uses the top apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeY.lean#L493-L496
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeY.lean#L493-L496

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

theorem Formalism.GM.FrozenVariableComponents.top_apply (LL : Letters N) (i : Fin N) (c d : Fin r) (F : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    top p LL i c d F = if LL.vec i then X (i, c) * pderiv (i, d) F else -(X (i, d) * pderiv (i, c) F) := by sorry
