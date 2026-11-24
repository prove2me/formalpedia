-- Prove2me | Theorems.Thm_Formalism_L2_Th1_G_pderiv_divPow
-- name    : Formalism.L2.Th1.G.pderiv_divPow
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T21:45:51.363213+00:00
-- url     : https://prove2.me/theorems/d3855073-baba-4665-ac51-9070f576b7ff
-- title:
--   G: pderiv div Pow
-- statement:
--   The G construction uses the pderiv div Pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/RamifiedCurveKernels/PairedSquareJets/Hurwitz.lean#L167-L184
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/RamifiedCurveKernels/PairedSquareJets/Hurwitz.lean#L167-L184

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

theorem Formalism.L2.Th1.G.pderiv_divPow (a : MvPowerSeries ι K) (i : ι) (m : ℕ) :
    MvPowerSeries.pderiv K i (MvPowerSeries.C (((m + 1).factorial : K)⁻¹) * a ^ (m + 1)) =
      (MvPowerSeries.C ((m.factorial : K)⁻¹) * a ^ m) * MvPowerSeries.pderiv K i a := by sorry
