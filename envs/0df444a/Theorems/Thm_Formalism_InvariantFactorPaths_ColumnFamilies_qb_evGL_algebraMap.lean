-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qb_evGL_algebraMap
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qb_evGL_algebraMap
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:36:41.528813+00:00
-- url     : https://prove2.me/theorems/a033bc5f-5a6c-4aa5-b318-9153fdbab9a6
-- title:
--   Column Families: qb ev GL algebra Map
-- statement:
--   The Column Families construction uses the qb ev GL algebra Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/BCoreT.lean#L11-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/BCoreT.lean#L11-L14

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_BCoreW
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_BCoreT
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
variable {n : ℕ}

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qb_evGL_algebraMap {R : Type} [CommRing R] (g : GL (Fin n) R) (P : MvPolynomial (Fin n × Fin n) ℤ) :
    evGL g (algebraMap _ (GLCoord ℤ n) P) =
      MvPolynomial.eval₂Hom (Int.castRingHom R) (fun ab : Fin n × Fin n => g.val ab.1 ab.2) P := by sorry
