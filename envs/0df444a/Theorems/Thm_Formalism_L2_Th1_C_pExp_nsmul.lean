-- Prove2me | Theorems.Thm_Formalism_L2_Th1_C_pExp_nsmul
-- name    : Formalism.L2.Th1.C.pExp_nsmul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:12:35.592808+00:00
-- url     : https://prove2.me/theorems/7d4ca09e-9f93-46d6-aada-af1e67694720
-- title:
--   C: p Exp nsmul
-- statement:
--   The C construction uses the p Exp nsmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/HasSecondLogDerivPowerSeriesExp.lean#L28-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/HasSecondLogDerivPowerSeriesExp.lean#L28-L34

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_IntBinomScalar
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_ChordSecondLogDeriv
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_HasSecondLogDerivPowerSeriesExp
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
open PowerSeries
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.C
variable {K : Type} [Field K] [CharZero K]

theorem Formalism.L2.Th1.C.pExp_nsmul (hE : MvExpLaws) (f : PowerSeries K) (hf : constantCoeff f = 0) (k : ℕ) :
    pExp (k • f) = pExp f ^ k := by sorry
