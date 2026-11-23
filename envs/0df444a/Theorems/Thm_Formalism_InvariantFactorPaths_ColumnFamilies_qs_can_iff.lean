-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_can_iff
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qs_can_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:51:53.19287+00:00
-- url     : https://prove2.me/theorems/c04096e0-58da-4291-a565-8d99d7afc7b0
-- title:
--   Column Families: qs can iff
-- statement:
--   The Column Families construction uses the qs can iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QsColHStrip.lean#L122-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QsColHStrip.lean#L122-L152

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QsColHHigh
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QsColHStrip
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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qs_can_iff {lam kap : Fin n → ℤ} {b : ℕ} (hl : Dominant lam) (hk : Dominant kap) (hs : HStrip lam kap b)
    (m : ↥(qs_D lam kap) → Fin n) :
    ((∀ c : ↥(qs_D lam kap), m c ∈ qs_ext kap (canT kap) c.1) ∧
      qs_ext lam (canT lam) = qs_rem (qs_D lam kap) (qs_ext kap (canT kap)) m) ↔ m = qs_mc lam kap := by sorry
