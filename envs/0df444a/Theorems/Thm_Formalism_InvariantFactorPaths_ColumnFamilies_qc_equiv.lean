-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qc_equiv
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qc_equiv
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T03:48:34.987251+00:00
-- url     : https://prove2.me/theorems/443985da-7849-499c-81fc-ed12b12aaefb
-- title:
--   Column Families: qc equiv
-- statement:
--   The Column Families construction uses the qc equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QcEvGLGenPtInt.lean#L127-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QcEvGLGenPtInt.lean#L127-L143

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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qc_equiv (hA : LemmaA) (hS : SBasis) (hmu : Dominant mu) (hβ : IsSMu M mu β)
    (ph : Matrix M.ι (TIdx mu) ℤ) (hph : ∀ I, ∑ i, ph i I • β i = brk mu I) :
    M.A * ph.map (Int.castRingHom _) = ph.map (Int.castRingHom _) * TMat mu := by sorry
