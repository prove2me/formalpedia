-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_lhwin_nonneg
-- name    : Formalism.GradedWeylDivisibility.lhwin_nonneg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:23:20.410815+00:00
-- url     : https://prove2.me/theorems/ba66888d-6192-4a93-bcb4-0767872efd7f
-- title:
--   Graded Weyl Divisibility: lhwin nonneg
-- statement:
--   The Graded Weyl Divisibility construction uses the lhwin nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LHwinLemmas.lean#L127-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LHwinLemmas.lean#L127-L131

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

theorem Formalism.GradedWeylDivisibility.lhwin_nonneg {R : Type*} [CommRing R] {r n : ℕ} {g : MvPolynomial (Fin r × Fin n) R} {z : ℤ}
    (hg : g ≠ 0) (hz : IsWeightedHomogeneous (lhwinHt r n) g z) : 0 ≤ z := by sorry
