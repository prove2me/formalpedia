-- Prove2me | Theorems.Thm_Formalism_L2_Th1_G_jetsIn_C
-- name    : Formalism.L2.Th1.G.jetsIn_C
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T21:43:50.440842+00:00
-- url     : https://prove2.me/theorems/fef9574f-6d20-47ae-9f31-b22b0e18996b
-- title:
--   G: jets In C
-- statement:
--   The G construction uses the jets In C property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/RamifiedCurveKernels/PairedSquareJets/Hurwitz.lean#L44-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/RamifiedCurveKernels/PairedSquareJets/Hurwitz.lean#L44-L50

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
variable {K : Type} [Field K] {R : Subring K} {ι : Type}

theorem Formalism.L2.Th1.G.jetsIn_C {c : K} (hc : c ∈ R) : JetsIn R (MvPowerSeries.C c : MvPowerSeries ι K) := by sorry
