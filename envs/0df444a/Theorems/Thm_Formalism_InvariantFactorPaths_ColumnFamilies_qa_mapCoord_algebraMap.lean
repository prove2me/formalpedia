-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qa_mapCoord_algebraMap
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qa_mapCoord_algebraMap
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T10:39:19.601573+00:00
-- url     : https://prove2.me/theorems/68564a28-ecbd-46f4-9898-1eca653586fd
-- title:
--   Column Families: qa map Coord algebra Map
-- statement:
--   The Column Families construction uses the qa map Coord algebra Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/ABridge.lean#L82-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/ABridge.lean#L82-L87

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QaExpEqBidetExp
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_ABridge
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_algebraMap

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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qa_mapCoord_algebraMap {n : ℕ} (F : Type) [CommRing F] (f : MvPolynomial (Fin n × Fin n) ℤ) :
    mapCoord (n := n) F (algebraMap _ (GLCoord ℤ n) f) =
      algebraMap _ (GLCoord F n) (MvPolynomial.map (Int.castRingHom F) f) := by sorry
