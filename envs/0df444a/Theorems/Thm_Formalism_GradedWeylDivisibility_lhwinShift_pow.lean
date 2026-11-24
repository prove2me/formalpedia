-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_lhwinShift_pow
-- name    : Formalism.GradedWeylDivisibility.lhwinShift_pow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:20:38.796027+00:00
-- url     : https://prove2.me/theorems/b9878aea-a4b2-478e-8e1c-f5f0ff2f0a17
-- title:
--   Graded Weyl Divisibility: lhwin Shift pow
-- statement:
--   The Graded Weyl Divisibility construction uses the lhwin Shift pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LHwinLemmas.lean#L37-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LHwinLemmas.lean#L37-L42

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

theorem Formalism.GradedWeylDivisibility.lhwinShift_pow {R : Type*} [CommRing R] {r n : ℕ}
    {P : Polynomial (MvPolynomial (Fin r × Fin n) R)} {μ δ : ℤ}
    (hP : LhwinShift P μ δ) (e : ℕ) : LhwinShift (P ^ e) (e • μ) δ := by sorry
