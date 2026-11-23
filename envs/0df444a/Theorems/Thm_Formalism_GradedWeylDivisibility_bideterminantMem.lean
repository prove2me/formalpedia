-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_bideterminantMem
-- name    : Formalism.GradedWeylDivisibility.bideterminantMem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:51:50.789989+00:00
-- url     : https://prove2.me/theorems/65cac145-9225-4d37-ae3a-d60c446f4108
-- title:
--   Graded Weyl Divisibility: bideterminant Mem
-- statement:
--   The Graded Weyl Divisibility construction uses the bideterminant Mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/BideterminantMem.lean#L17-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/BideterminantMem.lean#L17-L23

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LBidetLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LBidetMinor
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_BideterminantMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.GradedWeylDivisibility

theorem Formalism.GradedWeylDivisibility.bideterminantMem : BideterminantMem := by sorry
