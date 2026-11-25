-- Prove2me | Theorems.Thm_Formalism_L2_Th1_B_Split_split_vanishing_at_two
-- name    : Formalism.L2.Th1.B.Split.split_vanishing_at_two
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T02:45:34.024952+00:00
-- url     : https://prove2.me/theorems/2bddece0-d599-587e-9ffa-3cadfdeece7c
-- title:
--   Split: split vanishing at two
-- statement:
--   The Split construction uses the split vanishing at two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/BiextensionFormalMulMul.lean#L101-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/BiextensionFormalMulMul.lean#L101-L130

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_FirstLevelFromUniversalLaw
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_StatementT
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_BiextensionFormalMulMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B Formalism.L2.Th1.B.Split
open Formalism.L2.Th1.C Formalism.L2.Th1.C.Pts Formalism.L2.Th1.C.Calc
variable {K : Type} [Field K] [CharZero K] {R : Subring K} {l linv ph : PowerSeries K}

theorem Formalism.L2.Th1.B.Split.split_vanishing_at_two : Formalism.L2.Th1.G.SplitVanishTwo := by sorry
