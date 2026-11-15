-- Prove2me | Theorems.Thm_APFB07b_realized_protocol_unique_at_its_bill
-- name    : APFB07b.realized_protocol_unique_at_its_bill
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-14T06:07:52.351688+00:00
-- url     : https://prove2.me/theorems/a2dd6b5f-834e-414a-b418-d3e6dbe8ee88
-- title:
--   Realized protocol unique at its bill
-- statement:
--   Assume A2Selection and BWUniqueMinimum at the same supplied protocol-service-and-budget binding. Any admissible protocol with bill equal to the realized protocol’s bill is that realized protocol. This is uniqueness on the supplied protocol domain.
-- source:
--   Sib v44 Theorems/Thm_APFB07a_protocol_binding.lean:79

import Definitions.Def_APFB07a_ProtocolBinding
import Mathlib.Tactic.Linarith

set_option autoImplicit false

open APFPaper1.Source

theorem APFB07b.realized_protocol_unique_at_its_bill {D P R Record : Type*}
    (wholeResource : P → R) (calibration : R → NNReal) (maintained : P → Set Record)
    (sufficient : P → Set Record → D → Prop) (usesToRealize : P → D → Set Record → Prop)
    (C : ℝ) (realized : Finset D → P)
    (hA2 : APFB07a.A2Selection (Interface := Finset D) (Configuration := fun _ => P)
      (fun S p => APFB07a.protocolAdmissible wholeResource calibration maintained sufficient
        usesToRealize C S p)
      (fun _ p => APFB07a.protocolBill wholeResource calibration p) realized)
    (hBW : APFB07b.BWUniqueMinimum (Interface := Finset D) (Configuration := fun _ => P)
      (fun S p => APFB07a.protocolAdmissible wholeResource calibration maintained sufficient
        usesToRealize C S p)
      (fun _ p => APFB07a.protocolBill wholeResource calibration p))
    (S : Finset D) (p : P)
    (hp : APFB07a.protocolAdmissible wholeResource calibration maintained sufficient usesToRealize
      C S p)
    (hbill : APFB07a.protocolBill wholeResource calibration p =
      APFB07a.protocolBill wholeResource calibration (realized S)) : p = realized S := by sorry
