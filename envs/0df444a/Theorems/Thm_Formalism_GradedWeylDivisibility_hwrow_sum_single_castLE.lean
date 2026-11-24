-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_hwrow_sum_single_castLE
-- name    : Formalism.GradedWeylDivisibility.hwrow_sum_single_castLE
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:58:44.13384+00:00
-- url     : https://prove2.me/theorems/0fed9c54-705e-4fd6-880a-cdeea749888d
-- title:
--   Graded Weyl Divisibility: hwrow sum single cast LE
-- statement:
--   The Graded Weyl Divisibility construction uses the hwrow sum single cast LE property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LHwrowLemmas.lean#L19-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LHwrowLemmas.lean#L19-L44

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwrowLemmas
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GradedWeylDivisibility
open MvPolynomial

theorem Formalism.GradedWeylDivisibility.hwrow_sum_single_castLE {r s : ℕ} (hr : s ≤ r) (σ : Equiv.Perm (Fin s)) :
    (∑ q : Fin s, (Pi.single (Fin.castLE hr (σ q)) 1 : Fin r → ℕ)) =
      fun a => if a.val < s then 1 else 0 := by sorry
