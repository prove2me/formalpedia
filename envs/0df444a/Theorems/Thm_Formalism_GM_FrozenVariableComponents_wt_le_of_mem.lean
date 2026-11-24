-- Prove2me | Theorems.Thm_Formalism_GM_FrozenVariableComponents_wt_le_of_mem
-- name    : Formalism.GM.FrozenVariableComponents.wt_le_of_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:30:24.229984+00:00
-- url     : https://prove2.me/theorems/8949c5e9-af32-4ae7-80a1-82c3d896fd6d
-- title:
--   Frozen Variable Components: wt le of mem
-- statement:
--   The Frozen Variable Components construction uses the wt le of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeY.lean#L307-L312
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeY.lean#L307-L312

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

theorem Formalism.GM.FrozenVariableComponents.wt_le_of_mem (LL : Letters N) (j : ℕ) (M : WithTop ℤ) (F : MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hF : F ∈ YCond p LL j M) (m : Fin N × Fin r →₀ ℕ) (hm : m ∈ F.support) :
    ((wt LL j 0 m : ℤ) : WithTop ℤ) ≤ M := by sorry
