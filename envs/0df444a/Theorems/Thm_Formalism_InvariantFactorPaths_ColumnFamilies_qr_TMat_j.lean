-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qr_TMat_j
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qr_TMat_j
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:27:11.892918+00:00
-- url     : https://prove2.me/theorems/77da48e4-4b40-4dd5-a1b6-e1fc43c18379
-- title:
--   Column Families: qr TMat j
-- statement:
--   The Column Families construction uses the qr TMat j property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/KStableHighestWeightVector.lean#L99-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/KStableHighestWeightVector.lean#L99-L124

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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qr_TMat_j (hb : IsBlock h g1 t) (hl : Dominant lam) (hn : Dominant nu) (hi : Interl lam nu)
    (K' I' : TIdx nu) :
    evGL h (TMat lam (qr_j hi K') (qr_j hi I')) =
      ((t ^ (∑ a, lam a - ∑ a, nu a) : Rˣ) : R) * evGL g1 (TMat nu K' I') := by sorry
