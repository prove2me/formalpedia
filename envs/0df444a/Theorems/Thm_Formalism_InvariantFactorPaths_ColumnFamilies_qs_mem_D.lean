-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_mem_D
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qs_mem_D
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T21:41:58.478443+00:00
-- url     : https://prove2.me/theorems/917042fc-89a6-488f-8ba7-709b273eacf9
-- title:
--   Column Families: qs mem D
-- statement:
--   The Column Families construction uses the qs mem D property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QsColHStrip.lean#L60-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QsColHStrip.lean#L60-L71

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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qs_mem_D {lam kap : Fin n → ℤ} (hl : Dominant lam) (hk : Dominant kap) (c : ℤ) :
    c ∈ qs_D lam kap ↔ colH kap c = colH lam c + 1 := by sorry
