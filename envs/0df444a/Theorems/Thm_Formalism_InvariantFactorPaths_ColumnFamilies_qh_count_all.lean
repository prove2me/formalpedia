-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qh_count_all
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qh_count_all
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:21:50.716727+00:00
-- url     : https://prove2.me/theorems/ffaaa11d-f44e-4fe8-8b66-284606cf3da9
-- title:
--   Column Families: qh count all
-- statement:
--   The Column Families construction uses the qh count all property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QhCountAll.lean#L79-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QhCountAll.lean#L79-L144

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QhMemDualWeyl
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QhEquivOfCount
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QhCountAll
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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qh_count_all [NeZero n] {mu : Fin n → ℤ} (hmu : Dominant mu) (k : ℕ) (hk : 0 ≤ mu (lastIdx n) + k)
    {K : ℕ} (sz : Fin K → ℕ) (hsz : ∀ κ, sz κ ≤ n)
    (hshape : ∀ t : Fin n, (Formalism.GradedWeylDivisibility.shapeDeg sz t : ℤ) = mu t + k) (t : ℕ) :
    (univ.filter fun κ : {κ // 0 < sz κ} => t < sz κ.1).card =
      (univ.filter fun x : Fin (mu (lastIdx n) + k).toNat ⊕ ↥(TCols mu) =>
        t < Sum.elim (fun _ => n) (fun c : ↥(TCols mu) => colH mu c) x).card := by sorry
