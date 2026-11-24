-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qr_prod_G
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qr_prod_G
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:29:40.418206+00:00
-- url     : https://prove2.me/theorems/64dccd71-7472-4579-8674-1dd74ed63e69
-- title:
--   Column Families: qr prod G
-- statement:
--   The Column Families construction uses the qr prod G property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/KStableHighestWeightVector.lean#L59-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/KStableHighestWeightVector.lean#L59-L80

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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qr_prod_G (hn : Dominant nu) (hi : Interl lam nu) (K' I' : TIdx nu) :
    ∏ c ∈ TCols lam, qr_G g1 K' I' c =
      g1.val.det ^ (nu (lastIdx m) - lam (Fin.last m)).toNat *
        ∏ c : ↥(TCols nu), (g1.val.submatrix ((K' c).1.orderEmbOfFin (K' c).2)
          ((I' c).1.orderEmbOfFin (I' c).2)).det := by sorry
