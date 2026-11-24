-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_rowGenO_comp_colAddGen
-- name    : Formalism.GradedWeylDivisibility.rowGenO_comp_colAddGen
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:22:15.598796+00:00
-- url     : https://prove2.me/theorems/0bda83e1-84c7-4d7d-8a87-3412c45d16bf
-- title:
--   Graded Weyl Divisibility: row Gen O comp col Add Gen
-- statement:
--   The Graded Weyl Divisibility construction uses the row Gen O comp col Add Gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/RowDivStable.lean#L111-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/RowDivStable.lean#L111-L119

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LRowdivLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_RowDivStable
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

theorem Formalism.GradedWeylDivisibility.rowGenO_comp_colAddGen (R : Type*) [CommRing R] {r n : ℕ} (a b : Fin r) (l j : Fin n) :
    (rowGenO R a b).comp (colAddGen R (r := r) l j) =
      (Polynomial.mapAlgHom (colAddGen R (r := r) l j)).comp (rowGen R a b) := by sorry
