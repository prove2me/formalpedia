-- Prove2me | Theorems.Thm_Formalism_L2_Th1_G_jetsIn_subst_one
-- name    : Formalism.L2.Th1.G.jetsIn_subst_one
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T21:43:17.624766+00:00
-- url     : https://prove2.me/theorems/f36a1389-57ec-4034-a153-bd19eededf77
-- title:
--   G: jets In subst one
-- statement:
--   The G construction uses the jets In subst one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/RamifiedCurveKernels/PairedSquareJets/Hurwitz.lean#L212-L228
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/RamifiedCurveKernels/PairedSquareJets/Hurwitz.lean#L212-L228

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_StatementH
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_CoeffPowEqZeroOfCc
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_PairedSquareJets_Hurwitz
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_mfact_add_single

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
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.G
open Formalism.DworkPowerSeriesWeights (mfact JetsIntegral mfact_add_single)
variable {K : Type} [Field K] [CharZero K] {R : Subring K} {ι : Type}

theorem Formalism.L2.Th1.G.jetsIn_subst_one {f : PowerSeries K} {a : MvPowerSeries ι K} (hf : JetsIn1 R f)
    (h0 : MvPowerSeries.constantCoeff a = 0) (ha : JetsIn R a) :
    JetsIn R (PowerSeries.subst a f) := by sorry
