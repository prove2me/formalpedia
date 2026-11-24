-- Prove2me | Theorems.Thm_Formalism_GM_FrozenVariableComponents_freeze_pol
-- name    : Formalism.GM.FrozenVariableComponents.freeze_pol
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:14:22.819604+00:00
-- url     : https://prove2.me/theorems/3118497e-7c29-4654-9d87-b7cc910f3882
-- title:
--   Frozen Variable Components: freeze pol
-- statement:
--   The Frozen Variable Components construction uses the freeze pol property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeY.lean#L986-L1038
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeY.lean#L986-L1038

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

theorem Formalism.GM.FrozenVariableComponents.freeze_pol (LL : Letters N) (ρ : Fin r) (n : ℕ) (hn : LL.total ≤ n)
    (f : MvPolynomial (Fin N × Fin r) ℚ_[p]) (hf : f ∈ Pol p r LL) :
    freeze p LL ρ n f ∈ Pol p r (LL.snoc n) := by sorry
