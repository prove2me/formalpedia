-- Prove2me | Theorems.Thm_Formalism_L2_Th1_G_jetsIn_divPow
-- name    : Formalism.L2.Th1.G.jetsIn_divPow
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T21:44:12.678677+00:00
-- url     : https://prove2.me/theorems/394b0ff1-b77d-4d06-b76a-983921deeb92
-- title:
--   G: jets In div Pow
-- statement:
--   The G construction uses the jets In div Pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/RamifiedCurveKernels/PairedSquareJets/Hurwitz.lean#L186-L195
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/RamifiedCurveKernels/PairedSquareJets/Hurwitz.lean#L186-L195

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

theorem Formalism.L2.Th1.G.jetsIn_divPow {a : MvPowerSeries ι K} (h0 : MvPowerSeries.constantCoeff a = 0)
    (ha : JetsIn R a) (m : ℕ) : JetsIn R (MvPowerSeries.C ((m.factorial : K)⁻¹) * a ^ m) := by sorry
