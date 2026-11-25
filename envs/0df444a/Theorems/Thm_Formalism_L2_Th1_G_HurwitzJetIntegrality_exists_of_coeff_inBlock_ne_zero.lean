-- Prove2me | Theorems.Thm_Formalism_L2_Th1_G_HurwitzJetIntegrality_exists_of_coeff_inBlock_ne_zero
-- name    : Formalism.L2.Th1.G.HurwitzJetIntegrality.exists_of_coeff_inBlock_ne_zero
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T01:39:29.735605+00:00
-- url     : https://prove2.me/theorems/c662b785-4cf6-52a4-ae07-fde8fc3b250f
-- title:
--   Hurwitz Jet Integrality: exists of coeff in Block ne zero
-- statement:
--   The Hurwitz Jet Integrality construction uses the exists of coeff in Block ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/RamifiedCurveKernels/PairedSquareJets/HurwitzB.lean#L91-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/RamifiedCurveKernels/PairedSquareJets/HurwitzB.lean#L91-L100

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

theorem Formalism.L2.Th1.G.HurwitzJetIntegrality.exists_of_coeff_inBlock_ne_zero {K : Type} [Field K] {ι B : Type} (k : B)
    (f : MvPowerSeries ι K) (x : B × ι →₀ ℕ) (h : MvPowerSeries.coeff x (inBlock k f) ≠ 0) :
    ∃ m : ι →₀ ℕ, x = Finsupp.embDomain (blockEmb B ι k) m := by sorry
