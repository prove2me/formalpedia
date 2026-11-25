-- Prove2me | Theorems.Thm_Formalism_L2_Th1_G_jetsIn_prod
-- name    : Formalism.L2.Th1.G.jetsIn_prod
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T11:57:14.822246+00:00
-- url     : https://prove2.me/theorems/e7c344fb-7834-5e0e-af5e-3865101f6b9a
-- title:
--   G: jets In prod
-- statement:
--   The G construction uses the jets In prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/RamifiedCurveKernels/PairedSquareJets/Hurwitz.lean#L102-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/RamifiedCurveKernels/PairedSquareJets/Hurwitz.lean#L102-L105

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

theorem Formalism.L2.Th1.G.jetsIn_prod {α : Type} (s : Finset α) (f : α → MvPowerSeries ι K)
    (hf : ∀ a ∈ s, JetsIn R (f a)) : JetsIn R (∏ a ∈ s, f a) := by sorry
