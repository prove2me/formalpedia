-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LD_adjugate_adjugate_smul
-- name    : Formalism.CohomologicalDescent.LD.adjugate_adjugate_smul
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T23:06:50.167806+00:00
-- url     : https://prove2.me/theorems/ff449108-17a1-400e-b01e-b953b7e31deb
-- title:
--   LD: adjugate adjugate smul
-- statement:
--   The LD construction uses the adjugate adjugate smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HighestWeightProdLeadingMinors.lean#L606-L610
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HighestWeightProdLeadingMinors.lean#L606-L610

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

theorem Formalism.CohomologicalDescent.LD.adjugate_adjugate_smul {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n R) :
    A.det • A.adjugate.adjugate = A.det ^ (Fintype.card n - 1) • A := by sorry
