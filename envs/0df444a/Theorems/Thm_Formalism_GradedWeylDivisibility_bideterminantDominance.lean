-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_bideterminantDominance
-- name    : Formalism.GradedWeylDivisibility.bideterminantDominance
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T17:14:45.52369+00:00
-- url     : https://prove2.me/theorems/c3cb865a-3538-48d7-957d-c6f311228627
-- title:
--   Graded Weyl Divisibility: bideterminant Dominance
-- statement:
--   The Graded Weyl Divisibility construction uses the bideterminant Dominance property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/BideterminantDominance.lean#L10-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/BideterminantDominance.lean#L10-L31

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LBidetdomLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_BideterminantDominance
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Finset
noncomputable section
open Formalism Formalism.GradedWeylDivisibility

theorem Formalism.GradedWeylDivisibility.bideterminantDominance : BideterminantDominance := by sorry
