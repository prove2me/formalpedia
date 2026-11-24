-- Prove2me | Theorems.Thm_Formalism_L2_Th1_G_jet_pderiv
-- name    : Formalism.L2.Th1.G.jet_pderiv
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T21:45:01.987347+00:00
-- url     : https://prove2.me/theorems/4600a927-3972-4209-8975-b014c3d9b642
-- title:
--   G: jet pderiv
-- statement:
--   The G construction uses the jet pderiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/RamifiedCurveKernels/PairedSquareJets/Hurwitz.lean#L112-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/RamifiedCurveKernels/PairedSquareJets/Hurwitz.lean#L112-L118

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

theorem Formalism.L2.Th1.G.jet_pderiv (f : MvPowerSeries ι K) (i : ι) (κ : ι →₀ ℕ) :
    ((mfact κ : ℕ) : K) * MvPowerSeries.coeff κ (MvPowerSeries.pderiv K i f) =
      ((mfact (κ + Finsupp.single i 1) : ℕ) : K) *
        MvPowerSeries.coeff (κ + Finsupp.single i 1) f := by sorry
