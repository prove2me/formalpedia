-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_ldrow_coeff_rowAct_diag
-- name    : Formalism.GradedWeylDivisibility.ldrow_coeff_rowAct_diag
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T17:14:24.779785+00:00
-- url     : https://prove2.me/theorems/e6ec701c-f938-4d33-850d-d5769412170d
-- title:
--   Graded Weyl Divisibility: ldrow coeff row Act diag
-- statement:
--   The Graded Weyl Divisibility construction uses the ldrow coeff row Act diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LDrowLemmas.lean#L38-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LDrowLemmas.lean#L38-L50

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementD
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LDrowLemmas
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

theorem Formalism.GradedWeylDivisibility.ldrow_coeff_rowAct_diag {R : Type*} [CommRing R] {k n : ℕ} (t : Fin k → R)
    (f : MvPolynomial (Fin k × Fin n) R) (m : Fin k × Fin n →₀ ℕ) :
    coeff m (rowAct R (Matrix.diagonal t) f) = coeff m f * ∏ a : Fin k, t a ^ rowDeg m a := by sorry
