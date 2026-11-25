-- Prove2me | Theorems.Thm_Formalism_L2_Th1_G_HurwitzJetIntegrality_inBlock_eq_rename
-- name    : Formalism.L2.Th1.G.HurwitzJetIntegrality.inBlock_eq_rename
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T01:35:13.848714+00:00
-- url     : https://prove2.me/theorems/06ac88d9-5770-440e-8e13-f291f8dc0c90
-- title:
--   Hurwitz Jet Integrality: in Block eq rename
-- statement:
--   The Hurwitz Jet Integrality construction uses the in Block eq rename property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/RamifiedCurveKernels/PairedSquareJets/HurwitzB.lean#L65-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/RamifiedCurveKernels/PairedSquareJets/HurwitzB.lean#L65-L72

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

theorem Formalism.L2.Th1.G.HurwitzJetIntegrality.inBlock_eq_rename {K : Type} [Field K] {ι B : Type} (k : B) (f : MvPowerSeries ι K) :
    inBlock k f = MvPowerSeries.rename (blockEmb B ι k) f := by sorry
