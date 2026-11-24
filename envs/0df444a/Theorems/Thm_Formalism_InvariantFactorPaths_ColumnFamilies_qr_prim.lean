-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qr_prim
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qr_prim
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:21:09.81387+00:00
-- url     : https://prove2.me/theorems/63f28b21-3e0f-49e7-b7bd-343a15522052
-- title:
--   Column Families: qr prim
-- statement:
--   The Column Families construction uses the qr prim property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/ClosureBranching.lean#L10-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/ClosureBranching.lean#L10-L35

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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qr_prim {n : ℕ} [NeZero n] {M : GLMod n} {mu : Fin n → ℤ} {β : M.ι → GLCoord ℤ n}
    (hS : SBasis) (hmu : Dominant mu) (hβ : IsSMu M mu β)
    (ph : Matrix M.ι (TIdx mu) ℤ) (hph : ∀ I, ∑ i, ph i I • β i = brk mu I) (I0 : TIdx mu) (hI0 : StdT I0) (d : ℤ)
    (hd : ∀ i, d ∣ ph i I0) : d ∣ 1 := by sorry
