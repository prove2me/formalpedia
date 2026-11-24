-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LD_initial_minor_degree_le_one
-- name    : Formalism.CohomologicalDescent.LD.initial_minor_degree_le_one
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:06:05.769537+00:00
-- url     : https://prove2.me/theorems/6b521e12-7acd-4464-827a-68c9fa5764a4
-- title:
--   LD: initial minor degree le one
-- statement:
--   The LD construction uses the initial minor degree le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HighestWeightProdLeadingMinors.lean#L61-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HighestWeightProdLeadingMinors.lean#L61-L103

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

theorem Formalism.CohomologicalDescent.LD.initial_minor_degree_le_one {r s : ℕ} (I : Fin s → Fin r) (hs : s ≤ r) (a : Fin r)
    (m : Fin r × Fin r →₀ ℕ) (hm : m ∈ (initMinor ℤ I hs).support) :
    rowDeg m a ≤ if 0 < s then 1 else 0 := by sorry
