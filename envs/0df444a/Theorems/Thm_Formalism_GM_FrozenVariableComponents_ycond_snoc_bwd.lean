-- Prove2me | Theorems.Thm_Formalism_GM_FrozenVariableComponents_ycond_snoc_bwd
-- name    : Formalism.GM.FrozenVariableComponents.ycond_snoc_bwd
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T22:14:44.2817+00:00
-- url     : https://prove2.me/theorems/5915bc45-ad6d-44b1-acc5-1f4272eb3436
-- title:
--   Frozen Variable Components: ycond snoc bwd
-- statement:
--   The Frozen Variable Components construction uses the ycond snoc bwd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeY.lean#L350-L377
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeY.lean#L350-L377

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

theorem Formalism.GM.FrozenVariableComponents.ycond_snoc_bwd (LL : Letters N) (n j : ℕ) (hj : j ≤ N) (M : WithTop ℤ)
    (F : MvPolynomial (Fin (N + 1) × Fin r) ℚ_[p]) (hF : ∀ b, coeffη b F ∈ YCond p LL j M) :
    F ∈ YCond p (LL.snoc n) j M := by sorry
