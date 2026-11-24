-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_ps_left
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qs_ps_left
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:28:59.122497+00:00
-- url     : https://prove2.me/theorems/0a76b903-ee30-4cd7-9dbd-073b124d414f
-- title:
--   Column Families: qs ps left
-- statement:
--   The Column Families construction uses the qs ps left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/SymStrip.lean#L32-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/SymStrip.lean#L32-L96

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QsColHStrip
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_SymStrip
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
variable {n : ℕ} [NeZero n]
open Classical

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qs_ps_left (b : ℕ) {mu nu : Fin n → ℤ} (hmu : Dominant mu) (hnu : Dominant nu) (hs : HStrip mu nu b)
    (J : TIdx mu) (α : SymIdx n b) (K : TIdx nu) :
    ∑ y : TIdx mu × SymIdx n b, TMat mu J y.1 * SymMat n b α y.2 * ((qs_ps b mu nu y K : ℤ) : GLCoord ℤ n) =
      qs_mid b mu nu J α K := by sorry
