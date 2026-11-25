-- Prove2me | Theorems.Thm_Formalism_L2_Th1_G_HurwitzJetIntegrality_jetsIn_term
-- name    : Formalism.L2.Th1.G.HurwitzJetIntegrality.jetsIn_term
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T01:40:26.012785+00:00
-- url     : https://prove2.me/theorems/163e9611-3331-4181-9b1f-cca6eb30b7a6
-- title:
--   Hurwitz Jet Integrality: jets In term
-- statement:
--   The Hurwitz Jet Integrality construction uses the jets In term property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/RamifiedCurveKernels/PairedSquareJets/HurwitzB.lean#L21-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/RamifiedCurveKernels/PairedSquareJets/HurwitzB.lean#L21-L41

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
open Formalism.L2.Th1.G.HurwitzJetIntegrality

theorem Formalism.L2.Th1.G.HurwitzJetIntegrality.jetsIn_term (h1 : JetsRing) (h2 : JetsDivPow) {K : Type} [Field K] [CharZero K]
    (R : Subring K) {ι κ : Type} (f : MvPowerSeries ι K) (a : ι → MvPowerSeries κ K)
    (hf : JetsIn R f) (ha0 : ∀ i, MvPowerSeries.constantCoeff (a i) = 0)
    (ha : ∀ i, JetsIn R (a i)) (d : ι →₀ ℕ) :
    JetsIn R (MvPowerSeries.C (MvPowerSeries.coeff d f) * d.prod fun s e => (a s) ^ e) := by sorry
