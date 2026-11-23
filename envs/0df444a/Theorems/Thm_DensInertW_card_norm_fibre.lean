-- Prove2me | Theorems.Thm_DensInertW_card_norm_fibre
-- name    : DensInertW.card_norm_fibre
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:38:19.013954+00:00
-- url     : https://prove2.me/theorems/4b341ebd-2734-40d8-8714-f320aa1c830e
-- title:
--   Dens Inert W: card norm fibre
-- statement:
--   The Dens Inert W construction uses the card norm fibre property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InertDensity/ExistsTraceNeZero.lean#L86-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InertDensity/ExistsTraceNeZero.lean#L86-L141

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

theorem DensInertW.card_norm_fibre [DecidableEq L] (h2 : Module.finrank K L = 2) (a : L) (ha0 : a ≠ 0)
    (haq : a ^ Fintype.card K = a) :
    #{x : L | x ^ (Fintype.card K + 1) = a} = Fintype.card K + 1 := by sorry
