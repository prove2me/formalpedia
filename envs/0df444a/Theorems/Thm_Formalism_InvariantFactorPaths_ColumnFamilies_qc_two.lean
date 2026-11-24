-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qc_two
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qc_two
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:18:59.916679+00:00
-- url     : https://prove2.me/theorems/89b456a8-3791-40e2-bcd2-1a35ca6fe8a9
-- title:
--   Column Families: qc two
-- statement:
--   The Column Families construction uses the qc two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QcEvGLGenPtInt.lean#L102-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QcEvGLGenPtInt.lean#L102-L125

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QcEvGLDetUZpow
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QcEvGLGenPtInt
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
variable {n : ℕ} [NeZero n] {M : GLMod n} {mu : Fin n → ℤ} {β : M.ι → GLCoord ℤ n}

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qc_two (hβ : IsSMu M mu β) (ph : Matrix M.ι (TIdx mu) ℤ) (hph : ∀ I, ∑ i, ph i I • β i = brk mu I)
    {R : Type} [CommRing R] (x g : GL (Fin n) R) (I : TIdx mu) :
    ∑ j, evGL g ((M.A * ph.map (Int.castRingHom (GLCoord ℤ n)) : Matrix _ _ _) j I) * evGL x (β j) =
      ∑ j, evGL g ((ph.map (Int.castRingHom (GLCoord ℤ n)) * TMat mu : Matrix _ _ _) j I) * evGL x (β j) := by sorry
