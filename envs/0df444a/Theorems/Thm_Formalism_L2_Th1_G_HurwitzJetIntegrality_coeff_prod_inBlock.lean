-- Prove2me | Theorems.Thm_Formalism_L2_Th1_G_HurwitzJetIntegrality_coeff_prod_inBlock
-- name    : Formalism.L2.Th1.G.HurwitzJetIntegrality.coeff_prod_inBlock
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T01:39:51.0408+00:00
-- url     : https://prove2.me/theorems/989676c4-6db8-46ce-98d4-0fe5d0dde6eb
-- title:
--   Hurwitz Jet Integrality: coeff prod in Block
-- statement:
--   The Hurwitz Jet Integrality construction uses the coeff prod in Block property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/RamifiedCurveKernels/PairedSquareJets/HurwitzB.lean#L130-L186
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/RamifiedCurveKernels/PairedSquareJets/HurwitzB.lean#L130-L186

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

theorem Formalism.L2.Th1.G.HurwitzJetIntegrality.coeff_prod_inBlock {K : Type} [Field K] {ι B : Type} [Fintype B]
    (f : MvPowerSeries ι K) (κ : ι →₀ ℕ) :
    MvPowerSeries.coeff (rep B fun _ => κ) (∏ k : B, inBlock k f) =
      (MvPowerSeries.coeff κ f) ^ Fintype.card B := by sorry
