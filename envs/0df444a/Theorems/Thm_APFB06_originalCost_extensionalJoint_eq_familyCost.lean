-- Prove2me | Theorems.Thm_APFB06_originalCost_extensionalJoint_eq_familyCost
-- name    : APFB06.originalCost_extensionalJoint_eq_familyCost
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-14T05:59:21.320948+00:00
-- url     : https://prove2.me/theorems/06796551-8cb5-4f9b-bbf1-d74cc3efe844
-- title:
--   For a feasible family, original cost at the extensional class equals the extended-real embedding of family cost
-- statement:
--   For a feasible family, original cost at the extensional class equals the extended-real embedding of family cost.
-- source:
--   Paper 1 Supplement v9.28:1313-1322,1761-1766,1774-1885,2624-2625,2777-2782,7101

import Definitions.Def_APFB06_ExtensionalJoint
import Theorems.Thm_APFB06_occupant_subfamily_cost
import Mathlib.Data.ENNReal.Basic

set_option autoImplicit false
open APFPaper1.Source

namespace APFB06
end APFB06
open APFB06

theorem APFB06.originalCost_extensionalJoint_eq_familyCost {D P R Record : Type*}
    (wholeResource : P → R) (calibration : R → NNReal) (maintained : P → Set Record)
    (sufficient : P → Set Record → D → Prop) (usesToRealize : P → D → Set Record → Prop)
    (S : Finset D) (hf : familyFeasible maintained sufficient usesToRealize S) :
    originalCost (extensionalJoint maintained sufficient usesToRealize) wholeResource calibration S =
      ENNReal.ofReal (familyCost wholeResource calibration maintained sufficient usesToRealize S) := by sorry
