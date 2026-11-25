-- Prove2me | Theorems.Thm_Formalism_L2_Indef_IndefCoreR_tuple_is_base_or_member
-- name    : Formalism.L2.Indef.IndefCoreR.tuple_is_base_or_member
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T11:48:47.1634+00:00
-- url     : https://prove2.me/theorems/d41ae682-4f11-5925-8b1a-07d430c68f1d
-- title:
--   Indef Core R: tuple is base or member
-- statement:
--   The Indef Core R construction uses the tuple is base or member property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteForms/PairingConditionOfInverseMatrixIdentity.lean#L426-L430
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteForms/PairingConditionOfInverseMatrixIdentity.lean#L426-L430

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefSide
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefUse
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_PairingConditionOfInverseMatrixIdentity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Indef
open Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
variable {K : Type} [Field K] [NumberField K] [StarRing K]
open Formalism.L2.Indef.IndefCoreR
variable {Bs : DefBase K} {Df0 Df1 : DefSide Bs} {Dc : DefCols Df1} {Sp : SPer Dc} {N : IndefNum Bs}
  (P : IndefCoreR Df0 Df1 Dc Sp N)
include P

theorem Formalism.L2.Indef.IndefCoreR.tuple_is_base_or_member (h : ∀ t : Bs.Tup, t = Bs.μ0 ∨ ∃ w, P.base.μ w = t) : ∀ t : Bs.Tup, t = Bs.μ0 ∨ ∃ w, P.cols.μ w = t := by sorry
