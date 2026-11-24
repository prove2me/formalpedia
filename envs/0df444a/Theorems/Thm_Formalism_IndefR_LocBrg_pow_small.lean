-- Prove2me | Theorems.Thm_Formalism_IndefR_LocBrg_pow_small
-- name    : Formalism.IndefR.LocBrg.pow_small
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:53:26.486812+00:00
-- url     : https://prove2.me/theorems/b1413a60-eef8-4ab2-ad37-97b9527b6fc5
-- title:
--   Loc Brg: pow small
-- statement:
--   The Loc Brg construction uses the pow small property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/LocalNormSurjectivity/WittHS.lean#L17-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/LocalNormSurjectivity/WittHS.lean#L17-L33

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

theorem Formalism.IndefR.LocBrg.pow_small {γ : WithZero (Multiplicative ℤ)} (hγ : γ < 1) (δ : (WithZero (Multiplicative ℤ))ˣ) :
    ∃ N : ℕ, γ ^ N < δ := by sorry
