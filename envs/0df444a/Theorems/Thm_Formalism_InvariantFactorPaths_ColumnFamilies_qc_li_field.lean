-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qc_li_field
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qc_li_field
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:21:22.455171+00:00
-- url     : https://prove2.me/theorems/fcee70e9-0dcc-41f4-97b4-c02d91e9419c
-- title:
--   Column Families: qc li field
-- statement:
--   The Column Families construction uses the qc li field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QcEvGLGenPtInt.lean#L88-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QcEvGLGenPtInt.lean#L88-L100

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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qc_li_field (hA : LemmaA) (hS : SBasis) (hmu : Dominant mu) (hβ : IsSMu M mu β) (F : Type) [Field F] :
    LinearIndependent F (fun i => mapCoord (n := n) F (β i)) := by sorry
