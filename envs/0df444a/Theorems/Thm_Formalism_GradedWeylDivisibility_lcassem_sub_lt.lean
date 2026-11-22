-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_lcassem_sub_lt
-- name    : Formalism.GradedWeylDivisibility.lcassem_sub_lt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T16:48:58.455561+00:00
-- url     : https://prove2.me/theorems/25d12102-bf00-4671-83d8-644abeeb6d50
-- title:
--   Graded Weyl Divisibility: lcassem sub lt
-- statement:
--   The Graded Weyl Divisibility construction uses the lcassem sub lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LCassemLemmas.lean#L9-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LCassemLemmas.lean#L9-L23

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LCassemLemmas
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open Formalism Formalism.GradedWeylDivisibility
open scoped MonomialOrder

theorem Formalism.GradedWeylDivisibility.lcassem_sub_lt {σ R : Type*} [CommRing R] (o : MonomialOrder σ) {f g : MvPolynomial σ R}
    (hdeg : o.degree g = o.degree f) (hlc : o.leadingCoeff g = 1)
    (hne : f - o.leadingCoeff f • g ≠ 0) :
    o.degree (f - o.leadingCoeff f • g) ≺[o] o.degree f := by sorry
