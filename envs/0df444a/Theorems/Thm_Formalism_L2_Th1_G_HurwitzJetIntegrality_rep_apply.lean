-- Prove2me | Theorems.Thm_Formalism_L2_Th1_G_HurwitzJetIntegrality_rep_apply
-- name    : Formalism.L2.Th1.G.HurwitzJetIntegrality.rep_apply
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T01:34:18.072974+00:00
-- url     : https://prove2.me/theorems/21fbb317-7f26-4ae3-8654-891ac1db9ca9
-- title:
--   Hurwitz Jet Integrality: rep apply
-- statement:
--   The Hurwitz Jet Integrality construction uses the rep apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/RamifiedCurveKernels/PairedSquareJets/HurwitzB.lean#L105-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/RamifiedCurveKernels/PairedSquareJets/HurwitzB.lean#L105-L119

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

theorem Formalism.L2.Th1.G.HurwitzJetIntegrality.rep_apply (B : Type) [Fintype B] {ι : Type} (m : B → ι →₀ ℕ) (k : B) (i : ι) :
    rep B m (k, i) = m k i := by sorry
