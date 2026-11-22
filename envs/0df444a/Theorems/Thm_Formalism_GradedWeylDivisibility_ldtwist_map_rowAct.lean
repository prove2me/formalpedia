-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_ldtwist_map_rowAct
-- name    : Formalism.GradedWeylDivisibility.ldtwist_map_rowAct
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:36:21.224083+00:00
-- url     : https://prove2.me/theorems/008f2b6a-466e-4f0c-8421-32c18609de91
-- title:
--   Graded Weyl Divisibility: ldtwist map row Act
-- statement:
--   The Graded Weyl Divisibility construction uses the ldtwist map row Act property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/NablaLTwist.lean#L7-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/NablaLTwist.lean#L7-L18

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementD
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_NablaLTwist
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

theorem Formalism.GradedWeylDivisibility.ldtwist_map_rowAct {K L : Type*} [CommRing K] [CommRing L] (φ : K →+* L) {k n : ℕ}
    (g : Matrix (Fin k) (Fin k) K) (F : MvPolynomial (Fin k × Fin n) K) :
    map φ (rowAct K g F) = rowAct L (g.map φ) (map φ F) := by sorry
