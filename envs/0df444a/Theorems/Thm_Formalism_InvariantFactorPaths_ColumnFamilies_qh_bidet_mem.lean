-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qh_bidet_mem
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qh_bidet_mem
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:20:15.022275+00:00
-- url     : https://prove2.me/theorems/33e80ff7-e014-4ee6-bf84-abef93f76737
-- title:
--   Column Families: qh bidet mem
-- statement:
--   The Column Families construction uses the qh bidet mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QhCountAll.lean#L250-L357
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QhCountAll.lean#L250-L357

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QhMemDualWeyl
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QhEquivOfCount
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QhCountAll
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_algebraMap

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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qh_bidet_mem [NeZero n] {mu : Fin n → ℤ} (hmu : Dominant mu) (k : ℕ) (hk : 0 ≤ mu (lastIdx n) + k)
    {K : ℕ} (sz : Fin K → ℕ) (hsz : ∀ κ, sz κ ≤ n) (I : ∀ κ, Fin (sz κ) → Fin n)
    (hshape : ∀ t : Fin n, (Formalism.GradedWeylDivisibility.shapeDeg sz t : ℤ) = mu t + k) :
    ((qhDet R n ^ (-(k : ℤ)) : (GLCoord R n)ˣ) : GLCoord R n) *
      algebraMap _ (GLCoord R n) (rename Prod.swap (Formalism.GradedWeylDivisibility.bideterminant R sz hsz I)) ∈
      Submodule.span R (Set.range fun I : TIdx mu => mapCoord (n := n) R (brk mu I)) := by sorry
