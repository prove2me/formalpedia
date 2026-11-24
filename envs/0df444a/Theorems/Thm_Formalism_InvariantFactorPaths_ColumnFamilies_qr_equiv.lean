-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qr_equiv
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qr_equiv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:27:40.750785+00:00
-- url     : https://prove2.me/theorems/63b79ee7-5424-4792-84ca-ca0de6561e70
-- title:
--   Column Families: qr equiv
-- statement:
--   The Column Families construction uses the qr equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/ClosureBranching.lean#L37-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/ClosureBranching.lean#L37-L56

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_KStableHighestWeightVector
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_StripDataTensorColumnFamilies
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_ClosureBranching
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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qr_equiv {m : ℕ} [NeZero m] {M : GLMod (m + 1)} {lam : Fin (m + 1) → ℤ} {nu : Fin m → ℤ}
    (hl : Dominant lam) (hn : Dominant nu) (hi : Interl lam nu)
    (ph : Matrix M.ι (TIdx lam) ℤ)
    (hE : (M.A * ph.map (Int.castRingHom (GLCoord ℤ (m + 1))) : Matrix _ _ _) =
      (ph.map (Int.castRingHom (GLCoord ℤ (m + 1))) * TMat lam : Matrix _ _ _))
    {R : Type} [CommRing R] {h : GL (Fin (m + 1)) R} {g1 : GL (Fin m) R} {t : Rˣ} (hb : IsBlock h g1 t)
    (i : M.ι) (I' : TIdx nu) :
    ∑ k, evGL h (M.A i k) * ((ph k (qr_j hi I') : ℤ) : R) =
      ((t ^ (∑ a, lam a - ∑ a, nu a) : Rˣ) : R) *
        ∑ K' : TIdx nu, ((ph i (qr_j hi K') : ℤ) : R) * evGL g1 (TMat nu K' I') := by sorry
