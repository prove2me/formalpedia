-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_lehwShift_rowGen_monomial
-- name    : Formalism.GradedWeylDivisibility.lehwShift_rowGen_monomial
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:07:05.470129+00:00
-- url     : https://prove2.me/theorems/8b8a3271-0bbc-42fe-b6c1-d7441c362420
-- title:
--   Graded Weyl Divisibility: lehw Shift row Gen monomial
-- statement:
--   The Graded Weyl Divisibility construction uses the lehw Shift row Gen monomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LEhwLemmas.lean#L147-L155
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LEhwLemmas.lean#L147-L155

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

theorem Formalism.GradedWeylDivisibility.lehwShift_rowGen_monomial (R : Type*) [CommRing R] {r n : ℕ} (w : Fin r × Fin n → ℤ) (δ : ℤ)
    (a b : Fin r) (hstep : ∀ s : Fin n, w (a, s) = w (b, s) + δ) (d : Fin r × Fin n →₀ ℕ) (c : R) :
    LehwShift w (rowGen R a b (monomial d c)) (Finsupp.weight w d) δ := by sorry
