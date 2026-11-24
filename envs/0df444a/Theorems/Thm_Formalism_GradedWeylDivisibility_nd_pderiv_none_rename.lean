-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_nd_pderiv_none_rename
-- name    : Formalism.GradedWeylDivisibility.nd_pderiv_none_rename
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:22:18.621413+00:00
-- url     : https://prove2.me/theorems/eb571412-ce72-4e91-8955-04e1625730be
-- title:
--   Graded Weyl Divisibility: nd pderiv none rename
-- statement:
--   The Graded Weyl Divisibility construction uses the nd pderiv none rename property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/DualWeylNonDom.lean#L39-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/DualWeylNonDom.lean#L39-L44

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LNondomLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_DualWeylNonDom
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
variable {R : Type*} [CommRing R] {r n : ℕ}

theorem Formalism.GradedWeylDivisibility.nd_pderiv_none_rename (g : MvPolynomial (Fin r × Fin n) R) :
    pderiv none (rename (some : Fin r × Fin n → Option (Fin r × Fin n)) g) = 0 := by sorry
