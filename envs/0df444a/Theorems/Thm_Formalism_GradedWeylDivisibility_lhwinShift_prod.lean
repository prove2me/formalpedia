-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_lhwinShift_prod
-- name    : Formalism.GradedWeylDivisibility.lhwinShift_prod
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:20:44.157848+00:00
-- url     : https://prove2.me/theorems/688c99af-2e0c-4aa2-af3f-6b0d22bbd4c0
-- title:
--   Graded Weyl Divisibility: lhwin Shift prod
-- statement:
--   The Graded Weyl Divisibility construction uses the lhwin Shift prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LHwinLemmas.lean#L44-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LHwinLemmas.lean#L44-L53

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

theorem Formalism.GradedWeylDivisibility.lhwinShift_prod {R : Type*} [CommRing R] {r n : ℕ} {ι : Type*} (s : Finset ι)
    (P : ι → Polynomial (MvPolynomial (Fin r × Fin n) R)) (μ : ι → ℤ) (δ : ℤ)
    (h : ∀ i ∈ s, LhwinShift (P i) (μ i) δ) : LhwinShift (∏ i ∈ s, P i) (∑ i ∈ s, μ i) δ := by sorry
