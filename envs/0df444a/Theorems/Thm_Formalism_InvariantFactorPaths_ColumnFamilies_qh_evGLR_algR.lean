-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qh_evGLR_algR
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qh_evGLR_algR
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:19:25.926724+00:00
-- url     : https://prove2.me/theorems/db7c3bd3-b1e2-42d2-a336-e96df43cd700
-- title:
--   Column Families: qh ev GLR alg R
-- statement:
--   The Column Families construction uses the qh ev GLR alg R property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QhDetZpowMem.lean#L31-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QhDetZpowMem.lean#L31-L34

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_StatementH
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QhDetZpowMem
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
variable {n : ℕ} {R : Type} [CommRing R]

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qh_evGLR_algR {R' : Type} [CommRing R'] [Algebra R R'] (g : GL (Fin n) R') (r : R) :
    evGLR g (algebraMap R (GLCoord R n) r) = algebraMap R R' r := by sorry
