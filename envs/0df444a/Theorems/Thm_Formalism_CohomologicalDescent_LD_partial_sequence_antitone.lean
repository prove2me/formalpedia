-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LD_partial_sequence_antitone
-- name    : Formalism.CohomologicalDescent.LD.partial_sequence_antitone
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:06:30.361858+00:00
-- url     : https://prove2.me/theorems/39ba9961-95a8-409a-8c1a-c4074c6ffb1b
-- title:
--   LD: partial sequence antitone
-- statement:
--   The LD construction uses the partial sequence antitone property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HighestWeightProdLeadingMinors.lean#L851-L857
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HighestWeightProdLeadingMinors.lean#L851-L857

import Definitions.Def_Formalism_PieriBlockIdeals_LastGradedOfGradedAlone
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LastGradedImpliesOneBlock
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightShiftEqDetMul
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LEhwLemmas
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightProdLeadingMinors
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LD
open Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent.LA

theorem Formalism.CohomologicalDescent.LD.partial_sequence_antitone {r : ℕ} (ν : Fin r → ℕ) (hν : Antitone ν) (s : ℕ) : partialSumOfExponents ν (s + 1) ≤ partialSumOfExponents ν s := by sorry
