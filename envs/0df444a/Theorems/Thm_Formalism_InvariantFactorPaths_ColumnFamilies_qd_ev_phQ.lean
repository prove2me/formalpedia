-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qd_ev_phQ
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qd_ev_phQ
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T12:48:30.261912+00:00
-- url     : https://prove2.me/theorems/46a7d8d4-ced1-44c4-8a43-b89508179d6f
-- title:
--   Column Families: qd ev ph Q
-- statement:
--   The Column Families construction uses the qd ev ph Q property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/FiltrationTypeIntersection.lean#L42-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/FiltrationTypeIntersection.lean#L42-L45

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_HighestVectorsEqLattice
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_FiltrationTypeIntersection
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
variable [NeZero n]

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qd_ev_phQ {M : GLMod n} (CF : ColFam M) (j : CF.J) (nu : Fin n → ℤ) (w : TIdx (CF.mu j) → ℚ) (i : M.ι) :
    qb_ev M ℚ nu (qd_phQ CF j w) i = ∑ I, w I • qb_ev M ℚ nu (fun i => (CF.vec j I i : ℚ)) i := by sorry
