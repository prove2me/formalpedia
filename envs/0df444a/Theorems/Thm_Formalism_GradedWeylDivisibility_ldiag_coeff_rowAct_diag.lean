-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_ldiag_coeff_rowAct_diag
-- name    : Formalism.GradedWeylDivisibility.ldiag_coeff_rowAct_diag
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:59:54.26356+00:00
-- url     : https://prove2.me/theorems/49d8b9f9-81ce-4a01-834e-492d72d0ecc9
-- title:
--   Graded Weyl Divisibility: ldiag coeff row Act diag
-- statement:
--   The Graded Weyl Divisibility construction uses the ldiag coeff row Act diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/FockDiagBound.lean#L43-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/FockDiagBound.lean#L43-L55

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

theorem Formalism.GradedWeylDivisibility.ldiag_coeff_rowAct_diag {r n : ℕ} (t : Fin r → ℂ) (f : MvPolynomial (Fin r × Fin n) ℂ)
    (m : Fin r × Fin n →₀ ℕ) :
    coeff m (rowAct ℂ (Matrix.diagonal t) f) = coeff m f * ∏ a : Fin r, t a ^ rowDeg m a := by sorry
