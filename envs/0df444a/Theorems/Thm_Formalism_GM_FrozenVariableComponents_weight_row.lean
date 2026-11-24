-- Prove2me | Theorems.Thm_Formalism_GM_FrozenVariableComponents_weight_row
-- name    : Formalism.GM.FrozenVariableComponents.weight_row
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:14:24.674499+00:00
-- url     : https://prove2.me/theorems/4a35c753-ae05-42cd-b126-238bd1243b01
-- title:
--   Frozen Variable Components: weight row
-- statement:
--   The Frozen Variable Components construction uses the weight row property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeY.lean#L921-L931
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeY.lean#L921-L931

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
variable {K : Type*} [CommRing K]

theorem Formalism.GM.FrozenVariableComponents.weight_row {N r : ℕ} (i' : Fin N) (m : Fin N × Fin r →₀ ℕ) :
    Finsupp.weight (fun x : Fin N × Fin r => if x.1 = i' then 1 else 0) m = ∑ c, m (i', c) := by sorry
