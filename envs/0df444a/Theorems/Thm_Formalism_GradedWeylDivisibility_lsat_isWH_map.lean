-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_lsat_isWH_map
-- name    : Formalism.GradedWeylDivisibility.lsat_isWH_map
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:20:47.195473+00:00
-- url     : https://prove2.me/theorems/35018c01-fd54-4c41-8d63-be4b0ff3bc78
-- title:
--   Graded Weyl Divisibility: lsat is WH map
-- statement:
--   The Graded Weyl Divisibility construction uses the lsat is WH map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LSatLemmas.lean#L30-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LSatLemmas.lean#L30-L37

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LSatLemmas
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

theorem Formalism.GradedWeylDivisibility.lsat_isWH_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) {σ M : Type*}
    [AddCommMonoid M] (w : σ → M) (m : M) (f : MvPolynomial σ R)
    (hf : IsWeightedHomogeneous w f m) : IsWeightedHomogeneous w (map φ f) m := by sorry
