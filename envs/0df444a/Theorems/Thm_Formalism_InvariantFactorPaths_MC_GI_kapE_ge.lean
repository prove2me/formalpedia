-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_MC_GI_kapE_ge
-- name    : Formalism.InvariantFactorPaths.MC.GI.kapE_ge
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T11:50:27.354494+00:00
-- url     : https://prove2.me/theorems/c9fed778-a65c-51b2-b12b-2fd8b74b5798
-- title:
--   GI: kap E ge
-- statement:
--   The GI construction uses the kap E ge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/PartnerMeanCoordinates/PartnerMeanProofs/GamIntC.lean#L12-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/PartnerMeanCoordinates/PartnerMeanProofs/GamIntC.lean#L12-L13

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Definitions.Def_Formalism_ThetaLogCoordinates_PartnerMeanCoordinates_TheoremMCB
import Definitions.Def_Formalism_ThetaLogCoordinates_PartnerMeanCoordinates_PartnerMeanProofs_GamIntC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.MC Formalism.InvariantFactorPaths.MC.GI
open MvPolynomial Finset Formalism.GM Formalism.GM.M Formalism.GM.gammaIntegralityLemmas
variable {p : ℕ} [hp : Fact p.Prime]

theorem Formalism.InvariantFactorPaths.MC.GI.kapE_ge (N r B : ℕ) (_hr : 1 ≤ r) : (N + 4) * (r * B) + 6 * B ≤ kapE N r B := by sorry
