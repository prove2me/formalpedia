-- Prove2me | Theorems.Thm_Formalism_MainNotions_J_int_subst
-- name    : Formalism.MainNotions.J.int_subst
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T11:50:10.75346+00:00
-- url     : https://prove2.me/theorems/2a28d4e0-1c38-5ae6-a62f-b5b52b1a0965
-- title:
--   J: int subst
-- statement:
--   The J construction uses the int subst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/AdmissibleParameterJoins/GandSo.lean#L383-L386
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/AdmissibleParameterJoins/GandSo.lean#L383-L386

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

theorem Formalism.MainNotions.J.int_subst [Finite ι] (O : Subring K) (A : MvPowerSeries ι K) (hA : ∀ n, coeff n A ∈ O)
    (c : ι → MvPowerSeries κ K) (hc0 : ∀ i, constantCoeff (c i) = 0) (hc : ∀ i n, coeff n (c i) ∈ O) :
    ∀ n, coeff n (subst c A) ∈ O := by sorry
