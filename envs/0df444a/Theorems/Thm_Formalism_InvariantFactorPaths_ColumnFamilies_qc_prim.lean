-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qc_prim
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qc_prim
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:19:06.667114+00:00
-- url     : https://prove2.me/theorems/928aed2e-f9a4-4823-aaae-210eb8347374
-- title:
--   Column Families: qc prim
-- statement:
--   The Column Families construction uses the qc prim property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QcColHSuccLe.lean#L28-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QcColHSuccLe.lean#L28-L52

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QcEvGLGenPtInt
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QcColHSuccLe
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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qc_prim (hS : SBasis) (hmu : Dominant mu) (hβ : IsSMu M mu β)
    (ph : Matrix M.ι (TIdx mu) ℤ) (hph : ∀ I, ∑ i, ph i I • β i = brk mu I) (m : ℤ)
    (hm : ∀ i, m ∣ ph i (canT mu)) : m ∣ 1 := by sorry
