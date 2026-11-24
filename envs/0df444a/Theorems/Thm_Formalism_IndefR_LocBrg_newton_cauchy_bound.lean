-- Prove2me | Theorems.Thm_Formalism_IndefR_LocBrg_newton_cauchy_bound
-- name    : Formalism.IndefR.LocBrg.newton_cauchy_bound
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:17:18.522151+00:00
-- url     : https://prove2.me/theorems/de87505e-e93b-43dc-b51f-b7794592c8f9
-- title:
--   Loc Brg: newton cauchy bound
-- statement:
--   The Loc Brg construction uses the newton cauchy bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/LocalNormSurjectivity/WittHS.lean#L116-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/LocalNormSurjectivity/WittHS.lean#L116-L128

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

theorem Formalism.IndefR.LocBrg.newton_cauchy_bound (h2 : vv (2 : L) = 1) (hu : vv (u - 1) < 1) (n m : ℕ) (hnm : n ≤ m) :
    vv (newtonSq u m - newtonSq u n) ≤ vv (u - 1) ^ (n + 1) := by sorry
