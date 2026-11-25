-- Prove2me | Theorems.Thm_Formalism_L2_Th1_C_rescale_mvExp
-- name    : Formalism.L2.Th1.C.rescale_mvExp
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T11:48:53.695823+00:00
-- url     : https://prove2.me/theorems/f46488c9-dc25-4eb7-ae21-b111f9c8c39c
-- title:
--   C: rescale mv Exp
-- statement:
--   The C construction uses the rescale mv Exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/CoeffPowEqZeroOfCc.lean#L293-L303
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/CoeffPowEqZeroOfCc.lean#L293-L303

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

theorem Formalism.L2.Th1.C.rescale_mvExp {f : PowerSeries K} (hf : PowerSeries.constantCoeff f = 0) (c : K) :
    PowerSeries.rescale c (mvExp f : PowerSeries K) = mvExp (PowerSeries.rescale c f) := by sorry
