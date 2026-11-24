-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_sfac_prod_le
-- name    : Formalism.HermitianLatticeCounting.P.sfac_prod_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:43:18.110813+00:00
-- url     : https://prove2.me/theorems/00a33757-3dcf-4301-a1dd-4f6b23d0bd43
-- title:
--   P: sfac prod le
-- statement:
--   The P construction uses the sfac prod le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/CoefficientLeOperatorNorm.lean#L947-L956
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/CoefficientLeOperatorNorm.lean#L947-L956

import Definitions.Def_Formalism_FlagUnipotentLattices_HalfDifferenceL1Bound
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_CoefficientLeOperatorNorm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S7 Finset MeasureTheory
open scoped ComplexOrder
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P

theorem Formalism.HermitianLatticeCounting.P.sfac_prod_le {ι : Type} (s : Finset ι) (j : ι → ℕ) :
    ∏ x ∈ s, sfac (j x) ≤ sfac (∑ x ∈ s, j x) := by sorry
