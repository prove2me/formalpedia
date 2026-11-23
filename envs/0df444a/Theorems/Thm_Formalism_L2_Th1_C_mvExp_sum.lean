-- Prove2me | Theorems.Thm_Formalism_L2_Th1_C_mvExp_sum
-- name    : Formalism.L2.Th1.C.mvExp_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:23:54.496207+00:00
-- url     : https://prove2.me/theorems/9c35176b-944b-493d-8583-3e9a9851f4e4
-- title:
--   C: mv Exp sum
-- statement:
--   The C construction uses the mv Exp sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/CoeffPowEqZeroOfCc.lean#L199-L211
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/CoeffPowEqZeroOfCc.lean#L199-L211

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

theorem Formalism.L2.Th1.C.mvExp_sum {ι : Type} (s : Finset ι) (f : ι → MvPowerSeries σ K)
    (hf : ∀ a ∈ s, MvPowerSeries.constantCoeff (f a) = 0) :
    mvExp (∑ a ∈ s, f a) = ∏ a ∈ s, mvExp (f a) := by sorry
