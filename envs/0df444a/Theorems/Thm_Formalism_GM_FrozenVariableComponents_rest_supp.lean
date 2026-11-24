-- Prove2me | Theorems.Thm_Formalism_GM_FrozenVariableComponents_rest_supp
-- name    : Formalism.GM.FrozenVariableComponents.rest_supp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:14:28.545468+00:00
-- url     : https://prove2.me/theorems/f7a0c267-3d55-4ac3-b545-42f9f9e1feb5
-- title:
--   Frozen Variable Components: rest supp
-- statement:
--   The Frozen Variable Components construction uses the rest supp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeY.lean#L549-L574
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeY.lean#L549-L574

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

theorem Formalism.GM.FrozenVariableComponents.rest_supp (LL : Letters N) (j : ℕ) (c d : Fin r) (F : MvPolynomial (Fin N × Fin r) ℚ_[p])
    (m : Fin N × Fin r →₀ ℕ) (hm : m ∈ (restAct p LL j c d F).support) :
    ∃ m0 ∈ F.support, wt LL j 0 m = wt LL j 0 m0 := by sorry
