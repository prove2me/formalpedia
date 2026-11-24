-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qr_j_surj
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qr_j_surj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:28:08.887973+00:00
-- url     : https://prove2.me/theorems/18640d0c-8645-4ecc-b986-6180af8dcfa1
-- title:
--   Column Families: qr j surj
-- statement:
--   The Column Families construction uses the qr j surj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/HighestWeightIntegral.lean#L137-L155
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/HighestWeightIntegral.lean#L137-L155

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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qr_j_surj (hn : Dominant nu) (hi : Interl lam nu) (K : TIdx lam)
    (hK : ∀ c : ↥(TCols lam), (Fin.last m ∈ (K c).1 ↔ colH lam c = colH nu c + 1)) :
    ∃ K' : TIdx nu, qr_j hi K' = K := by sorry
