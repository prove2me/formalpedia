-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qd_evGLR_mapCoord
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qd_evGLR_mapCoord
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:29:48.656847+00:00
-- url     : https://prove2.me/theorems/cc5728cb-2d7b-4bf6-ae1f-a9977602f2b1
-- title:
--   Column Families: qd ev GLR map Coord
-- statement:
--   The Column Families construction uses the qd ev GLR map Coord property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/EqSmulCanonicalOfUnipotentInvariant.lean#L14-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/EqSmulCanonicalOfUnipotentInvariant.lean#L14-L23

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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qd_evGLR_mapCoord {R' : Type} [CommRing R'] [Algebra ℚ R'] (x : GL (Fin n) R') (z : GLCoord ℤ n) :
    evGLR (R := ℚ) x (mapCoord ℚ z) = evGL x z := by sorry
