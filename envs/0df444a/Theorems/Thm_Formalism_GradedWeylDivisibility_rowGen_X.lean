-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_rowGen_X
-- name    : Formalism.GradedWeylDivisibility.rowGen_X
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:25:57.604346+00:00
-- url     : https://prove2.me/theorems/e351fc3a-f561-4522-bfb3-b4e63c463b1e
-- title:
--   Graded Weyl Divisibility: row Gen X
-- statement:
--   The Graded Weyl Divisibility construction uses the row Gen X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/HWRaise.lean#L10-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/HWRaise.lean#L10-L13

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LRowdivLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_HWRaise
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

theorem Formalism.GradedWeylDivisibility.rowGen_X (R : Type*) [CommRing R] {r n : ℕ} (a b : Fin r) (v : Fin r × Fin n) :
    rowGen R a b (X v) = Polynomial.C (X v) +
      (if v.1 = b then Polynomial.X * Polynomial.C (X (a, v.2)) else 0) := by sorry
