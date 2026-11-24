-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qk_D_shift
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qk_D_shift
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:21:35.862659+00:00
-- url     : https://prove2.me/theorems/5df9cce9-3082-4171-9e7f-ef7cd145f5e6
-- title:
--   Column Families: qk D shift
-- statement:
--   The Column Families construction uses the qk D shift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QkDetExpand.lean#L84-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QkDetExpand.lean#L84-L111

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QkDetExpand
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Polynomial
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qk_D_shift {n : ℕ} (v : Fin n → ℝ) (b : ℕ) :
    ∑ s ∈ powersetCard b (univ : Finset (Fin n)), qk_D (s.piecewise (fun i => v i - 1) v) =
      (n.choose b : ℝ) * qk_D v := by sorry
