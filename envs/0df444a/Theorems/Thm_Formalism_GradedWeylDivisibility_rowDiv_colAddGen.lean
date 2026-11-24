-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_rowDiv_colAddGen
-- name    : Formalism.GradedWeylDivisibility.rowDiv_colAddGen
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:22:22.620911+00:00
-- url     : https://prove2.me/theorems/a2d1107a-57de-44d6-be27-0b3e09bb99ab
-- title:
--   Graded Weyl Divisibility: row Div col Add Gen
-- statement:
--   The Graded Weyl Divisibility construction uses the row Div col Add Gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/RowDivStable.lean#L131-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/RowDivStable.lean#L131-L141

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

theorem Formalism.GradedWeylDivisibility.rowDiv_colAddGen (R : Type*) [CommRing R] {r n : ℕ} (a b : Fin r) (k : ℕ) (l j : Fin n)
    (f : MvPolynomial (Fin r × Fin n) R) (hf : colAddGen R l j f = rename some f) :
    colAddGen R l j (rowDiv R a b k f) = rename some (rowDiv R a b k f) := by sorry
