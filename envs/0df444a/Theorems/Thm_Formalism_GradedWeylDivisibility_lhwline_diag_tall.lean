-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_lhwline_diag_tall
-- name    : Formalism.GradedWeylDivisibility.lhwline_diag_tall
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:23:39.024682+00:00
-- url     : https://prove2.me/theorems/74e78f4c-bc1e-4f83-b733-77e1cc8f2d8c
-- title:
--   Graded Weyl Divisibility: lhwline diag tall
-- statement:
--   The Graded Weyl Divisibility construction uses the lhwline diag tall property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LHwlineLemmas.lean#L408-L421
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LHwlineLemmas.lean#L408-L421

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementB
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwrowLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwlineLemmas
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
variable {K : Type} [Field K] {r n : ℕ}

theorem Formalism.GradedWeylDivisibility.lhwline_diag_tall (ν : Fin n → ℕ) (s : Fin n) (hs : r ≤ s.val) (hνs : 0 < ν s)
    (g : MvPolynomial (Fin r × Fin n) K) (hg : IsWeightedHomogeneous (colW r n) g ν)
    (D : Fin r × Fin n → K) (hD : ∀ (a : Fin r) (j : Fin n), a.val ≠ j.val → D (a, j) = 0) :
    eval D g = 0 := by sorry
