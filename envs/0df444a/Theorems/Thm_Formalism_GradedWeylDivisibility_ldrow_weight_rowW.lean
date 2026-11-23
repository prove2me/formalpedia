-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_ldrow_weight_rowW
-- name    : Formalism.GradedWeylDivisibility.ldrow_weight_rowW
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:52:49.781061+00:00
-- url     : https://prove2.me/theorems/538b2387-99c9-47df-a61a-394f0a380628
-- title:
--   Graded Weyl Divisibility: ldrow weight row W
-- statement:
--   The Graded Weyl Divisibility construction uses the ldrow weight row W property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LDrowLemmas.lean#L52-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LDrowLemmas.lean#L52-L67

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementD
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LDrowLemmas
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

theorem Formalism.GradedWeylDivisibility.ldrow_weight_rowW {k n : ℕ} (m : Fin k × Fin n →₀ ℕ) (a : Fin k) :
    Finsupp.weight (rowW k n) m a = rowDeg m a := by sorry
