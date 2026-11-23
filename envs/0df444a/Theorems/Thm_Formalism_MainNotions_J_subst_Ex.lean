-- Prove2me | Theorems.Thm_Formalism_MainNotions_J_subst_Ex
-- name    : Formalism.MainNotions.J.subst_Ex
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:20:35.358949+00:00
-- url     : https://prove2.me/theorems/654c9f48-0b66-4ca1-9363-2ab15f30c7fb
-- title:
--   J: subst Ex
-- statement:
--   The J construction uses the subst Ex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/AdmissibleParameterJoins/GandSo.lean#L175-L177
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/AdmissibleParameterJoins/GandSo.lean#L175-L177

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
variable {ι κ : Type} {K K' : Type} [Field K] [CharZero K] [Field K'] [CharZero K']

theorem Formalism.MainNotions.J.subst_Ex {c : ι → MvPowerSeries κ K} (hc : HasSubst c) {f : MvPowerSeries ι K}
    (hf : constantCoeff f = 0) : subst c (Ex f) = Ex (subst c f) := by sorry
