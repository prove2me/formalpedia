-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_lclosedeq_applyWord_map
-- name    : Formalism.GradedWeylDivisibility.lclosedeq_applyWord_map
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T18:01:38.990806+00:00
-- url     : https://prove2.me/theorems/48231f64-70bb-4332-b067-852feb8e55aa
-- title:
--   Graded Weyl Divisibility: lclosedeq apply Word map
-- statement:
--   The Graded Weyl Divisibility construction uses the lclosedeq apply Word map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LClosedeqLemmas.lean#L28-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LClosedeqLemmas.lean#L28-L35

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementB
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LClosedeqLemmas
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

theorem Formalism.GradedWeylDivisibility.lclosedeq_applyWord_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) {r n : ℕ}
    (w : List (Fin r × Fin r × ℕ)) (f : MvPolynomial (Fin r × Fin n) R) :
    applyWord S w (map φ f) = map φ (applyWord R w f) := by sorry
