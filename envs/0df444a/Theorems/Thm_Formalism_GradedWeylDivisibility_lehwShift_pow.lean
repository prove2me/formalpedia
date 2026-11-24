-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_lehwShift_pow
-- name    : Formalism.GradedWeylDivisibility.lehwShift_pow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:07:08.190684+00:00
-- url     : https://prove2.me/theorems/e2f02fd9-4b3a-478f-a186-73bdea4634c0
-- title:
--   Graded Weyl Divisibility: lehw Shift pow
-- statement:
--   The Graded Weyl Divisibility construction uses the lehw Shift pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LEhwLemmas.lean#L82-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LEhwLemmas.lean#L82-L89

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwlineLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwrowLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_DualWeylDominanceOf
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LEhwLemmas
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

theorem Formalism.GradedWeylDivisibility.lehwShift_pow {R : Type*} [CommRing R] {r n : ℕ} {w : Fin r × Fin n → ℤ}
    {P : Polynomial (MvPolynomial (Fin r × Fin n) R)} {μ δ : ℤ}
    (hP : LehwShift w P μ δ) (e : ℕ) : LehwShift w (P ^ e) (e • μ) δ := by sorry
