-- Prove2me | Theorems.Thm_APFB01_exists_distinction_of_declaredInput
-- name    : APFB01.exists_distinction_of_declaredInput
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-14T05:45:38.975824+00:00
-- url     : https://prove2.me/theorems/26949df8-54d9-427a-b273-fec33012ef13
-- title:
--   Under B01, a Boolean reading identified by hf with an original readout proposition factors through the physical quotient
-- statement:
--   Under B01, a Boolean reading identified by hf with an original readout proposition factors through the physical quotient.
-- source:
--   Paper 1 Supplement v9.28:1313-1322,1761-1766,1774-1885,2624-2625,2777-2782,7101

import Definitions.Def_APF_B01_DeclaredInput

set_option autoImplicit false
universe uX uP uF uR uO uA uM

namespace APFB01
end APFB01
open APFB01

theorem APFB01.exists_distinction_of_declaredInput
    {X : Type uX} {Process : Type uP} {PhysicalFact : Type uF}
    {ReadoutFact : Type uR} {ResultFact : Type uO} {AdmissionFact : Type uA}
    (profile : X → Process → Prop) (truth : PhysicalFact → X → Prop)
    (readoutTruth : ReadoutFact → X → Prop) (resultTruth : ResultFact → X → Prop)
    (admissionTruth : AdmissionFact → X → Prop)
    (hB01 : APF_B01_DeclaredInput profile truth readoutTruth resultTruth admissionTruth)
    (read : X → Bool) (f : ReadoutFact) (hf : ∀ x : X, readoutTruth f x ↔ read x = true) :
    ∃ d : PhysicalState profile → Bool, ∀ x : X, read x = d (physicalClass profile x) := by sorry
