-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_lehwShift_prod
-- name    : Formalism.GradedWeylDivisibility.lehwShift_prod
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:07:24.99643+00:00
-- url     : https://prove2.me/theorems/9e11e9a3-b522-44fe-9f19-773a20110bc1
-- title:
--   Graded Weyl Divisibility: lehw Shift prod
-- statement:
--   The Graded Weyl Divisibility construction uses the lehw Shift prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LEhwLemmas.lean#L91-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LEhwLemmas.lean#L91-L102

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

theorem Formalism.GradedWeylDivisibility.lehwShift_prod {R : Type*} [CommRing R] {r n : ℕ} {w : Fin r × Fin n → ℤ} {ι : Type*}
    (s : Finset ι) (P : ι → Polynomial (MvPolynomial (Fin r × Fin n) R)) (μ : ι → ℤ) (δ : ℤ)
    (h : ∀ i ∈ s, LehwShift w (P i) (μ i) δ) : LehwShift w (∏ i ∈ s, P i) (∑ i ∈ s, μ i) δ := by sorry
