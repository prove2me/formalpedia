-- Prove2me | Theorems.Thm_DensInertW_frob_sub
-- name    : DensInertW.frob_sub
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T09:38:58.387202+00:00
-- url     : https://prove2.me/theorems/ae6b2ad8-33dc-4b33-9b77-947f05da74df
-- title:
--   Dens Inert W: frob sub
-- statement:
--   The Dens Inert W construction uses the frob sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InertDensity/ExistsTraceNeZero.lean#L28-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InertDensity/ExistsTraceNeZero.lean#L28-L30

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

theorem DensInertW.frob_sub (x y : L) :
    (x - y) ^ Fintype.card K = x ^ Fintype.card K - y ^ Fintype.card K := by sorry
