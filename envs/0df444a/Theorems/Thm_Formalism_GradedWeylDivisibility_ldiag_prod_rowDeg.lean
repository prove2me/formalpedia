-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_ldiag_prod_rowDeg
-- name    : Formalism.GradedWeylDivisibility.ldiag_prod_rowDeg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:59:58.185026+00:00
-- url     : https://prove2.me/theorems/b1056dd2-6b97-4022-95b5-0ae7ff079af4
-- title:
--   Graded Weyl Divisibility: ldiag prod row Deg
-- statement:
--   The Graded Weyl Divisibility construction uses the ldiag prod row Deg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/FockDiagBound.lean#L25-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/FockDiagBound.lean#L25-L33

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

theorem Formalism.GradedWeylDivisibility.ldiag_prod_rowDeg {r n : ℕ} (t : Fin r → ℂ) (u : Fin r × Fin n →₀ ℕ) :
    (u.prod fun v k => t v.1 ^ k) = ∏ a : Fin r, t a ^ rowDeg u a := by sorry
