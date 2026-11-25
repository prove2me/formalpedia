-- Prove2me | Theorems.Thm_Formalism_L2_Th1_G_HurwitzJetIntegrality_mfact_rep
-- name    : Formalism.L2.Th1.G.HurwitzJetIntegrality.mfact_rep
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T01:39:02.948613+00:00
-- url     : https://prove2.me/theorems/09196d60-8954-4b5f-ac04-1d6b01200d11
-- title:
--   Hurwitz Jet Integrality: mfact rep
-- statement:
--   The Hurwitz Jet Integrality construction uses the mfact rep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/RamifiedCurveKernels/PairedSquareJets/HurwitzB.lean#L121-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/RamifiedCurveKernels/PairedSquareJets/HurwitzB.lean#L121-L128

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

theorem Formalism.L2.Th1.G.HurwitzJetIntegrality.mfact_rep (B : Type) [Fintype B] {ι : Type} [Fintype ι] (κ : ι →₀ ℕ) :
    mfact (rep B fun _ => κ) = (mfact κ) ^ Fintype.card B := by sorry
