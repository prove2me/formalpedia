-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qr_j_inj
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qr_j_inj
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:20:43.962328+00:00
-- url     : https://prove2.me/theorems/22aa1d86-b0c5-445e-b961-10902d653545
-- title:
--   Column Families: qr j inj
-- statement:
--   The Column Families construction uses the qr j inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/HighestWeightIntegral.lean#L129-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/HighestWeightIntegral.lean#L129-L135

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_HighestWeightSpaceFinite
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_HighestWeightIntegral
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
variable {m : ℕ} [NeZero m] {lam : Fin (m + 1) → ℤ} {nu : Fin m → ℤ}

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qr_j_inj (hi : Interl lam nu) : Function.Injective (qr_j (lam := lam) hi) := by sorry
