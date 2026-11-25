-- Prove2me | Theorems.Thm_Formalism_GM_FrozenVariableComponents_ycond_snoc_fwd
-- name    : Formalism.GM.FrozenVariableComponents.ycond_snoc_fwd
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:14:41.289118+00:00
-- url     : https://prove2.me/theorems/ad8b5668-e81e-4247-9323-4fca7d9bb849
-- title:
--   Frozen Variable Components: ycond snoc fwd
-- statement:
--   The Frozen Variable Components construction uses the ycond snoc fwd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeY.lean#L340-L348
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeY.lean#L340-L348

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

theorem Formalism.GM.FrozenVariableComponents.ycond_snoc_fwd (LL : Letters N) (n j : ℕ) (hj : j ≤ N) (M : WithTop ℤ) (b : Fin r →₀ ℕ)
    (F : MvPolynomial (Fin (N + 1) × Fin r) ℚ_[p]) (hF : F ∈ YCond p (LL.snoc n) j M) :
    coeffη b F ∈ YCond p LL j M := by sorry
