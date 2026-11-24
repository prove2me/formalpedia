-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_lehwShift_mul
-- name    : Formalism.GradedWeylDivisibility.lehwShift_mul
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:06:21.935802+00:00
-- url     : https://prove2.me/theorems/38594ac3-aa3c-4bfe-8c22-cc27617fa5c2
-- title:
--   Graded Weyl Divisibility: lehw Shift mul
-- statement:
--   The Graded Weyl Divisibility construction uses the lehw Shift mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LEhwLemmas.lean#L52-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LEhwLemmas.lean#L52-L64

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

theorem Formalism.GradedWeylDivisibility.lehwShift_mul {R : Type*} [CommRing R] {r n : ℕ} {w : Fin r × Fin n → ℤ}
    {P Q : Polynomial (MvPolynomial (Fin r × Fin n) R)} {μ μ' δ : ℤ}
    (hP : LehwShift w P μ δ) (hQ : LehwShift w Q μ' δ) : LehwShift w (P * Q) (μ + μ') δ := by sorry
