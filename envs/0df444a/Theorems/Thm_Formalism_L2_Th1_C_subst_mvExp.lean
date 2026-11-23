-- Prove2me | Theorems.Thm_Formalism_L2_Th1_C_subst_mvExp
-- name    : Formalism.L2.Th1.C.subst_mvExp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:24:03.352615+00:00
-- url     : https://prove2.me/theorems/50c7edb3-461d-4885-8fc7-60af15b03fab
-- title:
--   C: subst mv Exp
-- statement:
--   The C construction uses the subst mv Exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/CoeffPowEqZeroOfCc.lean#L274-L278
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/CoeffPowEqZeroOfCc.lean#L274-L278

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_IntBinomScalar
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_CoeffPowEqZeroOfCc
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
variable {K : Type} [Field K] [CharZero K] {σ : Type}

theorem Formalism.L2.Th1.C.subst_mvExp {f : PowerSeries K} {a : MvPowerSeries σ K}
    (hf : PowerSeries.constantCoeff f = 0) (ha : MvPowerSeries.constantCoeff a = 0) :
    PowerSeries.subst a (mvExp f : PowerSeries K) = mvExp (PowerSeries.subst a f) := by sorry
