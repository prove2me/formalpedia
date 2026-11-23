-- Prove2me | Theorems.Thm_DensInertW_card_fixed
-- name    : DensInertW.card_fixed
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:39:23.043178+00:00
-- url     : https://prove2.me/theorems/6aad0215-e60b-428a-9b8c-921b45858a5f
-- title:
--   Dens Inert W: card fixed
-- statement:
--   The Dens Inert W construction uses the card fixed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InertDensity/ExistsTraceNeZero.lean#L49-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InertDensity/ExistsTraceNeZero.lean#L49-L69

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

theorem DensInertW.card_fixed [DecidableEq L] : #{x : L | x ^ Fintype.card K = x} = Fintype.card K := by sorry
