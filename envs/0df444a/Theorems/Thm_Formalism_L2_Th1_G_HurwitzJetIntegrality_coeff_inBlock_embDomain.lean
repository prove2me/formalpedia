-- Prove2me | Theorems.Thm_Formalism_L2_Th1_G_HurwitzJetIntegrality_coeff_inBlock_embDomain
-- name    : Formalism.L2.Th1.G.HurwitzJetIntegrality.coeff_inBlock_embDomain
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T01:35:51.780803+00:00
-- url     : https://prove2.me/theorems/155f7a27-d422-445e-953c-faa3bef9ac5e
-- title:
--   Hurwitz Jet Integrality: coeff in Block emb Domain
-- statement:
--   The Hurwitz Jet Integrality construction uses the coeff in Block emb Domain property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/RamifiedCurveKernels/PairedSquareJets/HurwitzB.lean#L74-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/RamifiedCurveKernels/PairedSquareJets/HurwitzB.lean#L74-L89

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_StatementH
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_PhNormFromDatum
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_PairedSquareJets_HurwitzB
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
open Formalism.DworkPowerSeriesWeights (mfact JetsIntegral)
open HurwitzJetIntegrality
open Formalism.L2.Th1.G.HurwitzJetIntegrality

theorem Formalism.L2.Th1.G.HurwitzJetIntegrality.coeff_inBlock_embDomain {K : Type} [Field K] {ι B : Type} (k : B) (f : MvPowerSeries ι K)
    (κ : ι →₀ ℕ) :
    MvPowerSeries.coeff (Finsupp.embDomain (blockEmb B ι k) κ) (inBlock k f) =
      MvPowerSeries.coeff κ f := by sorry
