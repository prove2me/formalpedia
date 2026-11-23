-- Prove2me | Theorems.Thm_DensInertW_frob_add
-- name    : DensInertW.frob_add
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:39:47.388278+00:00
-- url     : https://prove2.me/theorems/4be4f2c0-0273-4442-a7e0-81fbb099f56b
-- title:
--   Dens Inert W: frob add
-- statement:
--   The Dens Inert W construction uses the frob add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InertDensity/ExistsTraceNeZero.lean#L23-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InertDensity/ExistsTraceNeZero.lean#L23-L25

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
omit [Fintype L]

theorem DensInertW.frob_add (x y : L) :
    (x + y) ^ Fintype.card K = x ^ Fintype.card K + y ^ Fintype.card K := by sorry
