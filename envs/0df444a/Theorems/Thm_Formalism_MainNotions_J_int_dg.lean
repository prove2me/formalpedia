-- Prove2me | Theorems.Thm_Formalism_MainNotions_J_int_dg
-- name    : Formalism.MainNotions.J.int_dg
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T09:57:09.54598+00:00
-- url     : https://prove2.me/theorems/b4b9e77e-c216-4106-a98b-881cb15188bd
-- title:
--   J: int dg
-- statement:
--   The J construction uses the int dg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/AdmissibleParameterJoins/GandSo.lean#L388-L394
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/AdmissibleParameterJoins/GandSo.lean#L388-L394

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_AdmissibleParameterJoins_GandSo
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.J
open MvPowerSeries
variable {ι κ : Type} {K : Type} [Field K]

theorem Formalism.MainNotions.J.int_dg (O : Subring K) (a : PowerSeries K) (ha : ∀ n, PowerSeries.coeff n a ∈ O) (i : ι) (n : ι →₀ ℕ) :
    coeff n (diagS a i : MvPowerSeries ι K) ∈ O := by sorry
