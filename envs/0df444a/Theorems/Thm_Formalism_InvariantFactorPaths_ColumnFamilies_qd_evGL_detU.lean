-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qd_evGL_detU
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qd_evGL_detU
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:31:28.253191+00:00
-- url     : https://prove2.me/theorems/bf0c7ed0-dc6a-4e72-a426-14adb199541e
-- title:
--   Column Families: qd ev GL det U
-- statement:
--   The Column Families construction uses the qd ev GL det U property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/EqSmulCanonicalOfUnipotentInvariant.lean#L63-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/EqSmulCanonicalOfUnipotentInvariant.lean#L63-L71

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_FiltrationTheoremOfClauses
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalB
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_EqSmulCanonicalOfUnipotentInvariant
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
open Formalism.GradedWeylDivisibility
variable {n : ℕ}

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qd_evGL_detU {R : Type} [CommRing R] (x : GL (Fin n) R) (m : ℤ) :
    evGL x ((detU n ^ m : (GLCoord ℤ n)ˣ) : GLCoord ℤ n) = ((Matrix.GeneralLinearGroup.det x ^ m : Rˣ) : R) := by sorry
