-- Prove2me | Theorems.Thm_Formalism_IndefR_LocBrg_newton_bound
-- name    : Formalism.IndefR.LocBrg.newton_bound
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:53:39.617043+00:00
-- url     : https://prove2.me/theorems/e83a6894-ffc9-4c39-8ec3-c84ce5334701
-- title:
--   Loc Brg: newton bound
-- statement:
--   The Loc Brg construction uses the newton bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/LocalNormSurjectivity/WittHS.lean#L66-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/LocalNormSurjectivity/WittHS.lean#L66-L99

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

theorem Formalism.IndefR.LocBrg.newton_bound (h2 : vv (2 : L) = 1) (hu : vv (u - 1) < 1) (k : ℕ) :
    vv (newtonSq u k - 1) < 1 ∧ vv (newtonSq u k * newtonSq u k - u) ≤ vv (u - 1) ^ (k + 1) := by sorry
