-- Prove2me | Theorems.Thm_Formalism_BehrendSets_E3_idx_eq
-- name    : Formalism.BehrendSets.E3.idx_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:10:04.21183+00:00
-- url     : https://prove2.me/theorems/8e2cec15-4fa8-4d6f-ad1c-eb1ec401ddc9
-- title:
--   E3: idx eq
-- statement:
--   The E3 construction uses the idx eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BehrendSets/BehrendVariance/SpaceFreeOfBehrendFree.lean#L11-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BehrendSets/BehrendVariance/SpaceFreeOfBehrendFree.lean#L11-L22

import Definitions.Def_Formalism_BehrendSets_StatementE
import Mathlib
import Definitions.Def_Formalism_BehrendSets_BehrendVariance_MulAbsSubLt
import Definitions.Def_Formalism_BehrendSets_BehrendVariance_SpaceFreeOfBehrendFree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Real
noncomputable section
open Formalism Formalism.BehrendSets Formalism.BehrendSets.E3

theorem Formalism.BehrendSets.E3.idx_eq {n Lw : ℕ} {h u t : ZMod n} (hord : Lw < addOrderOf h) {y : ℕ} {a b : ℤ}
    (hab : |a - b| ≤ (Lw : ℤ)) (ea : ((y : ℕ) : ZMod n) + u = t + a • h)
    (eb : ((y : ℕ) : ZMod n) + u = t + b • h) : a = b := by sorry
