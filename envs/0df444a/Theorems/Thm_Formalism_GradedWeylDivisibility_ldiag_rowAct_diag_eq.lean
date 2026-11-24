-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_ldiag_rowAct_diag_eq
-- name    : Formalism.GradedWeylDivisibility.ldiag_rowAct_diag_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:22:06.18984+00:00
-- url     : https://prove2.me/theorems/7aaa7fef-0587-4625-b72d-6ef39e4d25d7
-- title:
--   Graded Weyl Divisibility: ldiag row Act diag eq
-- statement:
--   The Graded Weyl Divisibility construction uses the ldiag row Act diag eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/FockDiagBound.lean#L13-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/FockDiagBound.lean#L13-L23

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_DomPow
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ProdFactorialSupportSubSingle
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockDiagBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Finset
noncomputable section
open Formalism Formalism.GradedWeylDivisibility
open Formalism.REAL (fockF)

theorem Formalism.GradedWeylDivisibility.ldiag_rowAct_diag_eq {r n : ℕ} (t : Fin r → ℂ) :
    rowAct ℂ (n := n) (Matrix.diagonal t) = aeval fun v : Fin r × Fin n => C (t v.1) * X v := by sorry
