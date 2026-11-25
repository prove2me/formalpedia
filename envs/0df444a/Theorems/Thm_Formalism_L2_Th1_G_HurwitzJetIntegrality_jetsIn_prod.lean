-- Prove2me | Theorems.Thm_Formalism_L2_Th1_G_HurwitzJetIntegrality_jetsIn_prod
-- name    : Formalism.L2.Th1.G.HurwitzJetIntegrality.jetsIn_prod
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T11:51:57.026465+00:00
-- url     : https://prove2.me/theorems/30c297fc-aa75-49bf-91d8-b71daf56068f
-- title:
--   Hurwitz Jet Integrality: jets In prod
-- statement:
--   The Hurwitz Jet Integrality construction uses the jets In prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/RamifiedCurveKernels/PairedSquareJets/HurwitzB.lean#L14-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/RamifiedCurveKernels/PairedSquareJets/HurwitzB.lean#L14-L19

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

theorem Formalism.L2.Th1.G.HurwitzJetIntegrality.jetsIn_prod (h1 : JetsRing) {K : Type} [Field K] (R : Subring K) {ι α : Type}
    (s : Finset α) (g : α → MvPowerSeries ι K) (hg : ∀ x ∈ s, JetsIn R (g x)) :
    JetsIn R (∏ x ∈ s, g x) := by sorry
