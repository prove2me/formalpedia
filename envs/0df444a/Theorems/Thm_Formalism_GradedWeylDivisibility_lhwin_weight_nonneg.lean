-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_lhwin_weight_nonneg
-- name    : Formalism.GradedWeylDivisibility.lhwin_weight_nonneg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:20:50.958084+00:00
-- url     : https://prove2.me/theorems/d200e297-ec99-4c1e-a11f-18e0f71ece4c
-- title:
--   Graded Weyl Divisibility: lhwin weight nonneg
-- statement:
--   The Graded Weyl Divisibility construction uses the lhwin weight nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LHwinLemmas.lean#L122-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LHwinLemmas.lean#L122-L125

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

theorem Formalism.GradedWeylDivisibility.lhwin_weight_nonneg {r n : ℕ} (d : Fin r × Fin n →₀ ℕ) :
    0 ≤ Finsupp.weight (lhwinHt r n) d := by sorry
