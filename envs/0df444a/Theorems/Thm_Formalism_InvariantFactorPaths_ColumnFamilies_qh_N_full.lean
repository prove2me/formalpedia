-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qh_N_full
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qh_N_full
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T11:41:54.995448+00:00
-- url     : https://prove2.me/theorems/e6b5194c-a997-4a05-96a7-8b16bc7b44be
-- title:
--   Column Families: qh N full
-- statement:
--   The Column Families construction uses the qh N full property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QhEquivOfCount.lean#L232-L246
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QhEquivOfCount.lean#L232-L246

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QhDetZpowMem
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QhEquivOfCount
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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qh_N_full (S : Finset (Fin n)) (hS : S.card = n) :
    qhN R n le_rfl (fun q => S.orderEmbOfFin hS q) = ((qhDet R n : (GLCoord R n)ˣ) : GLCoord R n) := by sorry
