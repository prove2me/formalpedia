-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_comb_roots_prod
-- name    : Formalism.CohomologicalDescent.comb_roots_prod
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:31:01.546365+00:00
-- url     : https://prove2.me/theorems/20006457-289d-40e0-92bd-e3131a2451bd
-- title:
--   Cohomological Descent: comb roots prod
-- statement:
--   The Cohomological Descent construction uses the comb roots prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/ContentLinkageHolds.lean#L12-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/ContentLinkageHolds.lean#L12-L21

import Mathlib
import Definitions.Def_Formalism_PieriBlockIdeals_Statement
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ContentLinkageHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Polynomial
open Formalism Formalism.CohomologicalDescent
open Classical

theorem Formalism.CohomologicalDescent.comb_roots_prod {K : Type} [Field K] {N : ℕ} (f : Fin N → K) :
    (∏ a, (X + C (f a))).roots = Multiset.map (fun a => -f a) Finset.univ.val := by sorry
