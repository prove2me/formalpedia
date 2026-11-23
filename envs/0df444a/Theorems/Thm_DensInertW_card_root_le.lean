-- Prove2me | Theorems.Thm_DensInertW_card_root_le
-- name    : DensInertW.card_root_le
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T09:38:23.39831+00:00
-- url     : https://prove2.me/theorems/e1ea8965-3c7e-407f-ae4f-a31206178c5f
-- title:
--   Dens Inert W: card root le
-- statement:
--   The Dens Inert W construction uses the card root le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InertDensity/ExistsTraceNeZero.lean#L76-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InertDensity/ExistsTraceNeZero.lean#L76-L84

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_ExistsTraceNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Polynomial
open DensInertW
variable {K L : Type} [Field K] [Fintype K] [Field L] [Fintype L] [Algebra K L]
omit [Fintype K] [Algebra K L]

theorem DensInertW.card_root_le [DecidableEq L] (n : ℕ) (a : L) : #{x : L | x ^ (n + 1) = a} ≤ n + 1 := by sorry
