-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_psD_left
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qs_psD_left
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:27:51.875954+00:00
-- url     : https://prove2.me/theorems/37cc1ddb-8bdf-4484-893c-2f21f6527c18
-- title:
--   Column Families: qs ps D left
-- statement:
--   The Column Families construction uses the qs ps D left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/SymDStrip.lean#L32-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/SymDStrip.lean#L32-L102

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_SymStrip
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_SymDStrip
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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qs_psD_left (b : ℕ) {mu nu : Fin n → ℤ} (hmu : Dominant mu) (hnu : Dominant nu) (hs : HStrip nu mu b)
    (J : TIdx mu) (α : SymIdx n b) (K : TIdx nu) :
    ∑ y : TIdx mu × SymIdx n b, TMat mu J y.1 * SymDMat n b α y.2 * ((qs_psD b mu nu y K : ℤ) : GLCoord ℤ n) =
      qs_midD b mu nu J α K := by sorry
