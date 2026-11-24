-- Prove2me | Theorems.Thm_Formalism_IndefR_LocBrg_pow_anti
-- name    : Formalism.IndefR.LocBrg.pow_anti
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:53:19.661846+00:00
-- url     : https://prove2.me/theorems/adb56b25-bb57-4ad2-9282-a694f8a70ee5
-- title:
--   Loc Brg: pow anti
-- statement:
--   The Loc Brg construction uses the pow anti property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/LocalNormSurjectivity/WittHS.lean#L111-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/LocalNormSurjectivity/WittHS.lean#L111-L114

import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_LocalNormSurjectivity_FinNormSurj
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_LocalNormSurjectivity_WittHS
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.IndefR Formalism.IndefR.LocBrg
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]
local notation "vv" => (Valued.v : Valuation L (WithZero (Multiplicative ℤ)))
variable (u : L)

theorem Formalism.IndefR.LocBrg.pow_anti {γ : WithZero (Multiplicative ℤ)} (hγ : γ ≤ 1) {a b : ℕ} (hab : a ≤ b) : γ ^ b ≤ γ ^ a := by sorry
