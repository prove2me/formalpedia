-- Prove2me | Theorems.Thm_Formalism_GM_FrozenVariableComponents_top_comm
-- name    : Formalism.GM.FrozenVariableComponents.top_comm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:42:31.872324+00:00
-- url     : https://prove2.me/theorems/21b5ecef-c32f-49ee-862e-595f8050c7b9
-- title:
--   Frozen Variable Components: top comm
-- statement:
--   The Frozen Variable Components construction uses the top comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeY.lean#L516-L523
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeY.lean#L516-L523

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

theorem Formalism.GM.FrozenVariableComponents.top_comm (LL : Letters N) (i i' : Fin N) (hi : i ≠ i') (c d c' d' : Fin r)
    (F : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    top p LL i c d (top p LL i' c' d' F) = top p LL i' c' d' (top p LL i c d F) := by sorry
