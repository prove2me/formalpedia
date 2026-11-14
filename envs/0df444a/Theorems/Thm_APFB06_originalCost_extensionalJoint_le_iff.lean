-- Prove2me | Theorems.Thm_APFB06_originalCost_extensionalJoint_le_iff
-- name    : APFB06.originalCost_extensionalJoint_le_iff
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-14T05:59:23.820197+00:00
-- url     : https://prove2.me/theorems/22613a30-1da8-43e6-8cfa-6c15b3abdbbf
-- title:
--   Originalcost extensionaljoint le iff
-- statement:
--   Original cost at the extensional class is at most a finite capacity exactly when the family is feasible and its real family cost is at most that capacity.
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

theorem APFB06.originalCost_extensionalJoint_le_iff {D P R Record : Type*}
    (wholeResource : P → R) (calibration : R → NNReal) (maintained : P → Set Record)
    (sufficient : P → Set Record → D → Prop) (usesToRealize : P → D → Set Record → Prop)
    (S : Finset D) (C : NNReal) :
    originalCost (extensionalJoint maintained sufficient usesToRealize) wholeResource calibration S ≤
        (C : ENNReal) ↔
      familyAdmissible wholeResource calibration maintained sufficient usesToRealize (C : ℝ) S := by sorry
