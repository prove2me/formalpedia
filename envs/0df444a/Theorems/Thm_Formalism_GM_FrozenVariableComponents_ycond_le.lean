-- Prove2me | Theorems.Thm_Formalism_GM_FrozenVariableComponents_ycond_le
-- name    : Formalism.GM.FrozenVariableComponents.ycond_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:14:33.343454+00:00
-- url     : https://prove2.me/theorems/18501089-1d0c-4e4f-bb87-c5f728f5deaa
-- title:
--   Frozen Variable Components: ycond le
-- statement:
--   The Frozen Variable Components construction uses the ycond le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeY.lean#L301-L305
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeY.lean#L301-L305

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

theorem Formalism.GM.FrozenVariableComponents.ycond_le (LL : Letters N) (j : ℕ) (M : WithTop ℤ) :
    YCond p (r := r) LL j M ≤ MvPolynomial.restrictSupport ℚ_[p]
        {m : Fin N × Fin r →₀ ℕ | ((wt LL j 0 m : ℤ) : WithTop ℤ) ≤ M} := by sorry
