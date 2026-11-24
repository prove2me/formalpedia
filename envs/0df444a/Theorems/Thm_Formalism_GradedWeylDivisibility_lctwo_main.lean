-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_lctwo_main
-- name    : Formalism.GradedWeylDivisibility.lctwo_main
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:59:35.769606+00:00
-- url     : https://prove2.me/theorems/2841e0ea-99ab-40e4-af47-3f587e1dd353
-- title:
--   Graded Weyl Divisibility: lctwo main
-- statement:
--   The Graded Weyl Divisibility construction uses the lctwo main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/TwoColumn.lean#L47-L208
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/TwoColumn.lean#L47-L208

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementC
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_TwoColumn
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

theorem Formalism.GradedWeylDivisibility.lctwo_main (h1 : PeelDecomp) (h2 : PeelHomog) (h3 : PeelLead) (h4 : PeelDegBound)
    (B : Type) [CommRing B] [IsDomain B] (r n : ℕ) (l j : Fin n) (hlj : l < j) :
    ∀ (d a0 s : ℕ) (ω : Fin r × Fin n →₀ ℕ) (g : MvPolynomial (Fin r × Fin n) B), r - a0 = d →
    g ≠ 0 → IsWeightedHomogeneous (pairW l j) g ω → (∀ b : Fin r, b.val < a0 → ω (b, l) = 0) →
    degreeOf none (colAddGen B l j g) ≤ s → InterlacedAt s l j ((colLex r n).degree g) := by sorry
