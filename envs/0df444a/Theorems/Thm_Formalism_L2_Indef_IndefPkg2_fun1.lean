-- Prove2me | Theorems.Thm_Formalism_L2_Indef_IndefPkg2_fun1
-- name    : Formalism.L2.Indef.IndefPkg2.fun1
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T11:46:08.312779+00:00
-- url     : https://prove2.me/theorems/3c34fdbd-2410-401d-8360-4a8fc1bc63b3
-- title:
--   Indef Pkg2: fun1
-- statement:
--   The Indef Pkg2 construction uses the fun1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteForms/PairingConditionOfInverseMatrixIdentity.lean#L160-L162
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteForms/PairingConditionOfInverseMatrixIdentity.lean#L160-L162

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefSide
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefUse
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_PairingConditionOfInverseMatrixIdentity
import Theorems.Thm_Formalism_L2_Indef_IndefCore_fun1

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
open Formalism.L2.Indef.IndefPkg2
variable {Bs : DefBase K} {A : DefAmb Bs} {fc : DefSub A → DefFace Bs} {cf : ConvFace Bs} {C CH : ℝ}
  (P : IndefPkg2 A fc cf C CH)

theorem Formalism.L2.Indef.IndefPkg2.fun1 (hde : 0 ≤ ((fc P.Zs).Z.num C CH).de) (hde3 : ((fc P.Zs).Z.num C CH).de ≤ 1 / 3) :
    P.core.cols.muMaxRR ≤ ((fc P.Zs).Z.num C CH).hh - meanLog P.core.cols.κ + 14 * ((fc P.Zs).Z.num C CH).la := by sorry
