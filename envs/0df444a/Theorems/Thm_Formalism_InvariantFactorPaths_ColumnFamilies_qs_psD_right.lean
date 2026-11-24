-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_psD_right
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qs_psD_right
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:29:27.810557+00:00
-- url     : https://prove2.me/theorems/c4f8da74-4a9d-4377-b579-841667880c25
-- title:
--   Column Families: qs ps D right
-- statement:
--   The Column Families construction uses the qs ps D right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/SymDStrip.lean#L105-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/SymDStrip.lean#L105-L141

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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qs_psD_right (b : ℕ) {mu nu : Fin n → ℤ} (hmu : Dominant mu) (hnu : Dominant nu) (hs : HStrip nu mu b)
    (J : TIdx mu) (α : SymIdx n b) (K : TIdx nu) :
    ∑ K' : TIdx nu, ((qs_psD b mu nu (J, α) K' : ℤ) : GLCoord ℤ n) * TMat nu K' K = qs_midD b mu nu J α K := by sorry
