-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_ndEul_homog
-- name    : Formalism.GradedWeylDivisibility.ndEul_homog
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:53:22.900787+00:00
-- url     : https://prove2.me/theorems/76315a94-349c-404d-a078-1667cbe55cef
-- title:
--   Graded Weyl Divisibility: nd Eul homog
-- statement:
--   The Graded Weyl Divisibility construction uses the nd Eul homog property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LNondomLemmas.lean#L58-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LNondomLemmas.lean#L58-L65

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LNondomLemmas
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
set_option linter.unusedSimpArgs false
variable {R : Type*} [CommRing R] {r n : ℕ}

theorem Formalism.GradedWeylDivisibility.ndEul_homog {g : MvPolynomial (Fin r × Fin n) R} {μ : Fin n → ℕ}
    (hg : IsWeightedHomogeneous (colW r n) g μ) (s : Fin n) :
    ndEul R r n s g = (μ s : R) • g := by sorry
