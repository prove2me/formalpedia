-- Prove2me | Theorems.Thm_Formalism_GM_FrozenVariableComponents_glAct_full_C
-- name    : Formalism.GM.FrozenVariableComponents.glAct_full_C
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:14:17.258362+00:00
-- url     : https://prove2.me/theorems/24c926e3-e4b4-4b92-9e1f-70b6de333e6c
-- title:
--   Frozen Variable Components: gl Act full C
-- statement:
--   The Frozen Variable Components construction uses the gl Act full C property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeY.lean#L616-L617
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeY.lean#L616-L617

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

theorem Formalism.GM.FrozenVariableComponents.glAct_full_C (LL : Letters N) (c d : Fin r) (a : ℚ_[p]) : glAct p LL N c d (C a) = 0 := by sorry
