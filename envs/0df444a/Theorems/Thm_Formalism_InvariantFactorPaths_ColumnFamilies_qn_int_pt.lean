-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qn_int_pt
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qn_int_pt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:21:33.398789+00:00
-- url     : https://prove2.me/theorems/18f4aa97-7849-4acc-bf72-232f98f6fd18
-- title:
--   Column Families: qn int pt
-- statement:
--   The Column Families construction uses the qn int pt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QnPtEmpty.lean#L60-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QnPtEmpty.lean#L60-L82

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwlineLemmas
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QnPtEmpty
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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qn_int_pt (n : ℕ) (W : Set (MvPolynomial (Fin n × Fin n) ℚ))
    (hW : ∀ F ∈ W, ∀ (a b : Fin n) (k : ℕ), a ≠ b → rowDiv ℚ a b k F ∈ W)
    (hev : ∀ F ∈ W, ∃ z : ℤ, eval (idFrame ℚ n n) F = z) (D : Finset (Fin n × Fin n)) :
    (∀ x ∈ D, x.2 < x.1) → ∀ F ∈ W, aeval (qn_pt n D) F ∈ qn_IntS n := by sorry
