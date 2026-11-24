-- Prove2me | Theorems.Thm_Formalism_GM_FrozenVariableComponents_glAct_full_mul
-- name    : Formalism.GM.FrozenVariableComponents.glAct_full_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:14:19.914018+00:00
-- url     : https://prove2.me/theorems/b612ce76-2db7-4665-9a58-0e46ce24630a
-- title:
--   Frozen Variable Components: gl Act full mul
-- statement:
--   The Frozen Variable Components construction uses the gl Act full mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeY.lean#L609-L614
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeY.lean#L609-L614

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

theorem Formalism.GM.FrozenVariableComponents.glAct_full_mul (LL : Letters N) (c d : Fin r) (F G : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    glAct p LL N c d (F * G) = F * glAct p LL N c d G + G * glAct p LL N c d F := by sorry
