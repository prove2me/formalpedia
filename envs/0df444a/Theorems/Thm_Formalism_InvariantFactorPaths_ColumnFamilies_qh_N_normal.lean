-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qh_N_normal
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qh_N_normal
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T11:41:40.284799+00:00
-- url     : https://prove2.me/theorems/a409996f-787d-5740-832c-f08d58261e7c
-- title:
--   Column Families: qh N normal
-- statement:
--   The Column Families construction uses the qh N normal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QhEquivOfCount.lean#L177-L230
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QhEquivOfCount.lean#L177-L230

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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qh_N_normal (s : ℕ) (hs : s ≤ n) (J : Fin s → Fin n) :
    ∃ (ε : R) (S : {S : Finset (Fin n) // S.card = s}),
      qhN R s hs J = ε • qhN R s hs (fun q => S.1.orderEmbOfFin S.2 q) := by sorry
