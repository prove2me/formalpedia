-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_nd_comm_EF
-- name    : Formalism.GradedWeylDivisibility.nd_comm_EF
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:20:47.2509+00:00
-- url     : https://prove2.me/theorems/79a7cc24-7922-4087-a0af-e0edec956f93
-- title:
--   Graded Weyl Divisibility: nd comm EF
-- statement:
--   The Graded Weyl Divisibility construction uses the nd comm EF property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LNondomLemmas.lean#L78-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LNondomLemmas.lean#L78-L94

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LNondomLemmas
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
set_option linter.unusedSimpArgs false
variable {R : Type*} [CommRing R] {r n : ℕ}

theorem Formalism.GradedWeylDivisibility.nd_comm_EF {l j : Fin n} (hlj : l ≠ j) (g : MvPolynomial (Fin r × Fin n) R) :
    ndE R r n l j (ndF R r n l j g) =
      ndF R r n l j (ndE R r n l j g) + (ndEul R r n l g - ndEul R r n j g) := by sorry
