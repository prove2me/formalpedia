-- Prove2me | Theorems.Thm_Formalism_L2_Th1_C_Clo_addDefect_add_right
-- name    : Formalism.L2.Th1.C.Clo.addDefect_add_right
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T04:22:27.124631+00:00
-- url     : https://prove2.me/theorems/2bcf2501-d9ea-44e3-a05a-176b9e97124a
-- title:
--   Clo: add Defect add right
-- statement:
--   The Clo construction uses the add Defect add right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/Closure.lean#L217-L222
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/Closure.lean#L217-L222

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_PhNormClosed
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_Points
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_SecondCoeffConsistency
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_Closure
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
open Finset
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.C
open Clo
open Formalism.L2.Th1.C.Clo
variable {K : Type} [Field K] {R : Subring K} {l linv : PowerSeries K}
variable [CharZero K] {ph : PowerSeries K} {σ : Type}

theorem Formalism.L2.Th1.C.Clo.addDefect_add_right (h1 : F1 R l linv ph) {x y y' : MvPowerSeries σ K} (hx : IsPt R x)
    (hy : IsPt R y) (hy' : IsPt R y') :
    LG R (be0 l linv ph x (fadd l linv y y') - (be0 l linv ph x y + be0 l linv ph x y')) := by sorry
