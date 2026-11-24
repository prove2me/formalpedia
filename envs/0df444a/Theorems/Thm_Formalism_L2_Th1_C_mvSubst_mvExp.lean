-- Prove2me | Theorems.Thm_Formalism_L2_Th1_C_mvSubst_mvExp
-- name    : Formalism.L2.Th1.C.mvSubst_mvExp
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T21:43:34.56792+00:00
-- url     : https://prove2.me/theorems/709ac725-28eb-460c-82f4-e08adff969ad
-- title:
--   C: mv Subst mv Exp
-- statement:
--   The C construction uses the mv Subst mv Exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/CoeffPowEqZeroOfCc.lean#L280-L291
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/CoeffPowEqZeroOfCc.lean#L280-L291

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

theorem Formalism.L2.Th1.C.mvSubst_mvExp {τ : Type} {f : MvPowerSeries σ K} {a : σ → MvPowerSeries τ K}
    (hf : MvPowerSeries.constantCoeff f = 0) (ha : MvPowerSeries.HasSubst a) :
    MvPowerSeries.subst a (mvExp f) = mvExp (MvPowerSeries.subst a f) := by sorry
