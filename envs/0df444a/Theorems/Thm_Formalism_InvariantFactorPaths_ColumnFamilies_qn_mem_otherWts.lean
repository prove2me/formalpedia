-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qn_mem_otherWts
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qn_mem_otherWts
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:29:14.978801+00:00
-- url     : https://prove2.me/theorems/05897e28-5b68-461c-b34e-5147ea2e2299
-- title:
--   Column Families: qn mem other Wts
-- statement:
--   The Column Families construction uses the qn mem other Wts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/CoeffTransposeVariables.lean#L80-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/CoeffTransposeVariables.lean#L80-L85

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_TransposeVariables
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockQHW
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_CoeffTransposeVariables
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
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
open Formalism.GradedWeylDivisibility

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qn_mem_otherWts (n : ℕ) (lam : Fin n → ℤ) (g : MvPolynomial (Fin n × Fin n) ℚ)
    (hg : ∀ m ∈ g.support, qn_wt m ≠ lam) : g ∈ otherWts (glOps ℚ n (rowLetters n) Set.univ) lam := by sorry
