-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_lclosedeq_rowGen_map
-- name    : Formalism.GradedWeylDivisibility.lclosedeq_rowGen_map
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:59:17.30648+00:00
-- url     : https://prove2.me/theorems/e3ec9ff1-2f5f-48fd-b478-1c89bc938d63
-- title:
--   Graded Weyl Divisibility: lclosedeq row Gen map
-- statement:
--   The Graded Weyl Divisibility construction uses the lclosedeq row Gen map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LClosedeqLemmas.lean#L10-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LClosedeqLemmas.lean#L10-L21

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

theorem Formalism.GradedWeylDivisibility.lclosedeq_rowGen_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) {r n : ℕ}
    (a b : Fin r) (f : MvPolynomial (Fin r × Fin n) R) :
    rowGen S a b (map φ f) = Polynomial.map (map φ) (rowGen R a b f) := by sorry
