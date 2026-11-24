-- Prove2me | Theorems.Thm_Formalism_GM_FrozenVariableComponents_glAct_full_X
-- name    : Formalism.GM.FrozenVariableComponents.glAct_full_X
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:14:14.466009+00:00
-- url     : https://prove2.me/theorems/ec0e11ca-a0b9-4841-9b79-f66c0adc13a2
-- title:
--   Frozen Variable Components: gl Act full X
-- statement:
--   The Frozen Variable Components construction uses the gl Act full X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeY.lean#L619-L636
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeY.lean#L619-L636

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

theorem Formalism.GM.FrozenVariableComponents.glAct_full_X (LL : Letters N) (c ρ : Fin r) (b : Fin N) (d : Fin r) :
    glAct p LL N c ρ (X (b, d)) =
      if LL.vec b then (if d = ρ then X (b, c) else 0) else (if d = c then -X (b, ρ) else 0) := by sorry
