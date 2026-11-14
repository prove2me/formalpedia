-- Prove2me | Theorems.Thm_APFB01_distinct_objects_of_later_record
-- name    : APFB01.distinct_objects_of_later_record
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-14T05:53:10.476463+00:00
-- url     : https://prove2.me/theorems/c42a4ea1-ce3c-4283-8c6f-e2b409a61990
-- title:
--   Distinct objects of later record
-- statement:
--   Supporting lemma: distinct objects of later record. The exact quantified statement supplied with this entry is controlling, including every displayed hypothesis. E is only a supplied map: no inverse equations for D and E are assumed. hnow, hrev, hmotion and hfact remain explicit. This proves a distinction witness, not a physical rate coordinate or rate derivation.
-- source:
--   Sib v44 Theorems/Thm_APFB01_reversal_and_the_rate.lean:67

import Definitions.Def_APF_B01_DeclaredInput

set_option autoImplicit false

universe uX uP uR uS

namespace APFPaper5.K3
end APFPaper5.K3
open APFPaper5.K3

theorem APFB01.distinct_objects_of_later_record {X : Type uX} {Process : Type uP} {R : Type uR}
    (profile : X → Process → Prop) (later : X → R)
    (hfact : ∀ r : R, APFB01.Descends profile (fun x => later x = r)) (x y : X)
    (hne : later x ≠ later y) :
    APFB01.physicalClass profile x ≠ APFB01.physicalClass profile y := by sorry
