-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_lclosedeq_lpMinor_map
-- name    : Formalism.GradedWeylDivisibility.lclosedeq_lpMinor_map
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:52:22.07656+00:00
-- url     : https://prove2.me/theorems/471ff52b-e4dd-4870-88b4-6a5beceede5c
-- title:
--   Graded Weyl Divisibility: lclosedeq lp Minor map
-- statement:
--   The Graded Weyl Divisibility construction uses the lclosedeq lp Minor map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LClosedeqLemmas.lean#L37-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LClosedeqLemmas.lean#L37-L44

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

theorem Formalism.GradedWeylDivisibility.lclosedeq_lpMinor_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) {r n : ℕ}
    (s : ℕ) (hr : s ≤ r) (hn : s ≤ n) :
    map φ (lpMinor R (r := r) (n := n) s hr hn) = lpMinor S s hr hn := by sorry
