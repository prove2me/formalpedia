-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_sum_single_castLE
-- name    : Formalism.GradedWeylDivisibility.sum_single_castLE
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T18:24:59.92655+00:00
-- url     : https://prove2.me/theorems/a59fca74-f2da-4c96-a9f7-93219a54b2b0
-- title:
--   Graded Weyl Divisibility: sum single cast LE
-- statement:
--   The Graded Weyl Divisibility construction uses the sum single cast LE property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LBidetMinor.lean#L12-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LBidetMinor.lean#L12-L35

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LBidetLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LBidetMinor
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

theorem Formalism.GradedWeylDivisibility.sum_single_castLE {n s : ℕ} (hs : s ≤ n) :
    (∑ q : Fin s, (Pi.single (Fin.castLE hs q) 1 : Fin n → ℕ)) = initW n s := by sorry
