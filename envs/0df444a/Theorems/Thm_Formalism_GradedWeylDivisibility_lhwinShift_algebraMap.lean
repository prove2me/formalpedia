-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_lhwinShift_algebraMap
-- name    : Formalism.GradedWeylDivisibility.lhwinShift_algebraMap
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:23:15.77118+00:00
-- url     : https://prove2.me/theorems/148c9c5b-097b-4d0d-ba4a-0c1cf71ef4b0
-- title:
--   Graded Weyl Divisibility: lhwin Shift algebra Map
-- statement:
--   The Graded Weyl Divisibility construction uses the lhwin Shift algebra Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LHwinLemmas.lean#L55-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LHwinLemmas.lean#L55-L63

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementB
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwinLemmas
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

theorem Formalism.GradedWeylDivisibility.lhwinShift_algebraMap {R : Type*} [CommRing R] {r n : ℕ} (c : R) (δ : ℤ) :
    LhwinShift (algebraMap R (Polynomial (MvPolynomial (Fin r × Fin n) R)) c) 0 δ := by sorry
