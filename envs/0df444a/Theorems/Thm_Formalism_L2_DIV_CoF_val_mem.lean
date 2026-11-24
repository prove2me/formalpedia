-- Prove2me | Theorems.Thm_Formalism_L2_DIV_CoF_val_mem
-- name    : Formalism.L2.DIV.CoF.val_mem
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T20:16:29.547165+00:00
-- url     : https://prove2.me/theorems/8cf21243-85b3-4d63-ac35-fdcbf7895311
-- title:
--   Co F: val mem
-- statement:
--   The Co F construction uses the val mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/ConjugationAtDistinguishedPlace.lean#L67-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/ConjugationAtDistinguishedPlace.lean#L67-L67

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_AdjoinCycZeta
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IotaABijective
import Definitions.Def_Formalism_QuotientMetricDivisors_RatHermLcvTwist
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ConjugationAtDistinguishedPlace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField
noncomputable section
open Formalism Formalism.L2 Formalism.L2.DIV
open Formalism.L2.Host Formalism.DivisionValues
open Formalism.L2.DIV.CoF
variable (ι : Qb →+* ℂ) (LL : Fld)

theorem Formalism.L2.DIV.CoF.val_mem (x : CoF ι LL) : val ι LL x ∈ LL := by sorry
