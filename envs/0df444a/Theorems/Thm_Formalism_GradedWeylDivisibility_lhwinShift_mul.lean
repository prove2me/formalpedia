-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_lhwinShift_mul
-- name    : Formalism.GradedWeylDivisibility.lhwinShift_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T17:01:08.795365+00:00
-- url     : https://prove2.me/theorems/669e72c1-fda1-4272-8170-2b65f225485c
-- title:
--   Graded Weyl Divisibility: lhwin Shift mul
-- statement:
--   The Graded Weyl Divisibility construction uses the lhwin Shift mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LHwinLemmas.lean#L15-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LHwinLemmas.lean#L15-L25

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

theorem Formalism.GradedWeylDivisibility.lhwinShift_mul {R : Type*} [CommRing R] {r n : ℕ}
    {P Q : Polynomial (MvPolynomial (Fin r × Fin n) R)} {μ μ' δ : ℤ}
    (hP : LhwinShift P μ δ) (hQ : LhwinShift Q μ' δ) : LhwinShift (P * Q) (μ + μ') δ := by sorry
