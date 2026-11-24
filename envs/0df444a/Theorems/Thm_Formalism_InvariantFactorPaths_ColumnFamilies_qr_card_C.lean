-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qr_card_C
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qr_card_C
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:27:16.641715+00:00
-- url     : https://prove2.me/theorems/e9ba960a-ac27-40e3-8c37-789e6a4b0e91
-- title:
--   Column Families: qr card C
-- statement:
--   The Column Families construction uses the qr card C property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/KStableHighestWeightVector.lean#L82-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/KStableHighestWeightVector.lean#L82-L97

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_HighestWeightIntegral
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_KStableHighestWeightVector
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
variable {m : ℕ} [NeZero m] {lam : Fin (m + 1) → ℤ} {nu : Fin m → ℤ} {R : Type} [CommRing R]
  {h : GL (Fin (m + 1)) R} {g1 : GL (Fin m) R} {t : Rˣ}

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qr_card_C (hl : Dominant lam) (hn : Dominant nu) (hi : Interl lam nu) :
    (((TCols lam).filter fun c => colH lam c = colH nu c + 1).card : ℤ) =
      ∑ a, lam a - ∑ a, nu a - lam (Fin.last m) := by sorry
