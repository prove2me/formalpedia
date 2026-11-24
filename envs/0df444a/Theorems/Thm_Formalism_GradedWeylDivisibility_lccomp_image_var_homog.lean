-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_lccomp_image_var_homog
-- name    : Formalism.GradedWeylDivisibility.lccomp_image_var_homog
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:58:42.580867+00:00
-- url     : https://prove2.me/theorems/02ce922b-59b3-4723-8469-917ef8f07531
-- title:
--   Graded Weyl Divisibility: lccomp image var homog
-- statement:
--   The Graded Weyl Divisibility construction uses the lccomp image var homog property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LCcompLemmas.lean#L19-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LCcompLemmas.lean#L19-L31

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementC
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LCcompLemmas
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

theorem Formalism.GradedWeylDivisibility.lccomp_image_var_homog {B : Type*} [CommRing B] {r n : ℕ} (l j : Fin n) (v : Fin r × Fin n) :
    IsWeightedHomogeneous (lccompW l j)
      ((if v.2 = j then X (some v) + X none * X (some (v.1, l)) else X (some v) :
        MvPolynomial (Option (Fin r × Fin n)) B)) (pairW l j v) := by sorry
