-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qr_sum_colH
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qr_sum_colH
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:22:20.771082+00:00
-- url     : https://prove2.me/theorems/6a3c1a78-42c0-4d60-8bbb-b203fb74cb15
-- title:
--   Column Families: qr sum col H
-- statement:
--   The Column Families construction uses the qr sum col H property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/HighestWeightIntegral.lean#L40-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/HighestWeightIntegral.lean#L40-L56

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
variable {m : ℕ} {lam : Fin (m + 1) → ℤ} {nu : Fin m → ℤ}

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qr_sum_colH {n : ℕ} (mu : Fin n → ℤ) (L U : ℤ) (h : ∀ a, L ≤ mu a ∧ mu a ≤ U) :
    ∑ c ∈ Finset.Ioc L U, (colH mu c : ℤ) = ∑ a, (mu a - L) := by sorry
