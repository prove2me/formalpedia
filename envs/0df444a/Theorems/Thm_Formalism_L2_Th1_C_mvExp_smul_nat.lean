-- Prove2me | Theorems.Thm_Formalism_L2_Th1_C_mvExp_smul_nat
-- name    : Formalism.L2.Th1.C.mvExp_smul_nat
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T21:49:07.896876+00:00
-- url     : https://prove2.me/theorems/ec154ea9-f6a4-401f-b758-db33c0a936c3
-- title:
--   C: mv Exp smul nat
-- statement:
--   The C construction uses the mv Exp smul nat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/CoeffPowEqZeroOfCc.lean#L219-L222
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/CoeffPowEqZeroOfCc.lean#L219-L222

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

theorem Formalism.L2.Th1.C.mvExp_smul_nat {f : MvPowerSeries σ K} (hf : MvPowerSeries.constantCoeff f = 0) (n : ℕ) :
    mvExp ((n : K) • f) = mvExp f ^ n := by sorry
