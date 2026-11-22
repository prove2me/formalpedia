-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_lsat_map_colAddGen
-- name    : Formalism.GradedWeylDivisibility.lsat_map_colAddGen
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T17:08:54.458309+00:00
-- url     : https://prove2.me/theorems/350070dd-ff5d-49f8-9fab-b900adb02354
-- title:
--   Graded Weyl Divisibility: lsat map col Add Gen
-- statement:
--   The Graded Weyl Divisibility construction uses the lsat map col Add Gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LSatLemmas.lean#L16-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LSatLemmas.lean#L16-L28

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

theorem Formalism.GradedWeylDivisibility.lsat_map_colAddGen {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) {r n : ℕ}
    (l j : Fin n) (f : MvPolynomial (Fin r × Fin n) R) :
    map φ (colAddGen R l j f) = colAddGen S l j (map φ f) := by sorry
