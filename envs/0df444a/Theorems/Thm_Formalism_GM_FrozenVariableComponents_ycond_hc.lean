-- Prove2me | Theorems.Thm_Formalism_GM_FrozenVariableComponents_ycond_hc
-- name    : Formalism.GM.FrozenVariableComponents.ycond_hc
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:14:32.897167+00:00
-- url     : https://prove2.me/theorems/c007554a-c439-4f2f-9aa9-fadd1464afc5
-- title:
--   Frozen Variable Components: ycond hc
-- statement:
--   The Frozen Variable Components construction uses the ycond hc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeY.lean#L585-L596
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeY.lean#L585-L596

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

theorem Formalism.GM.FrozenVariableComponents.ycond_hc (LL : Letters N) (j : ℕ) (M : WithTop ℤ) (t : ℕ)
    (F : MvPolynomial (Fin N × Fin r) ℚ_[p]) (hF : F ∈ YCond p LL j M) :
    homogeneousComponent t F ∈ YCond p LL j M := by sorry
