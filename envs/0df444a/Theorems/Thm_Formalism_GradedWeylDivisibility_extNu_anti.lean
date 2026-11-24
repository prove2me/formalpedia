-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_extNu_anti
-- name    : Formalism.GradedWeylDivisibility.extNu_anti
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:53:57.77922+00:00
-- url     : https://prove2.me/theorems/a82a245e-3133-4f60-8d6a-8fc4ed5f523d
-- title:
--   Graded Weyl Divisibility: ext Nu anti
-- statement:
--   The Graded Weyl Divisibility construction uses the ext Nu anti property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/HWRowWeight.lean#L10-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/HWRowWeight.lean#L10-L20

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwrowLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_HWRowWeight
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

theorem Formalism.GradedWeylDivisibility.extNu_anti {n : ℕ} {ν : Fin n → ℕ} (hν : Antitone ν) {i j : ℕ} (hij : i ≤ j) :
    hwrowExtNu ν j ≤ hwrowExtNu ν i := by sorry
