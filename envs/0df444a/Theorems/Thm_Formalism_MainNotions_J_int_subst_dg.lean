-- Prove2me | Theorems.Thm_Formalism_MainNotions_J_int_subst_dg
-- name    : Formalism.MainNotions.J.int_subst_dg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:16:07.661073+00:00
-- url     : https://prove2.me/theorems/913cd32c-d2a6-4673-9bea-849345766b7b
-- title:
--   J: int subst dg
-- statement:
--   The J construction uses the int subst dg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/AdmissibleParameterJoins/GandSo.lean#L403-L407
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/AdmissibleParameterJoins/GandSo.lean#L403-L407

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

theorem Formalism.MainNotions.J.int_subst_dg (O : Subring K) (A : MvPowerSeries ι K) (hA : ∀ n, coeff n A ∈ O) (a : PowerSeries K)
    (ha0 : PowerSeries.constantCoeff a = 0) (ha : ∀ n, PowerSeries.coeff n a ∈ O) :
    ∀ n, coeff n (subst (diagS a) A) ∈ O := by sorry
