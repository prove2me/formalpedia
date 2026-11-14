-- Prove2me | Theorems.Thm_APFB07a_familyCost_attained_of_A2
-- name    : APFB07a.familyCost_attained_of_A2
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-14T05:59:58.628068+00:00
-- url     : https://prove2.me/theorems/03a70653-f3f3-43e6-8990-af946d361bc5
-- title:
--   Protocol-bound selection attains the family infimum
-- statement:
--   Assume A2Selection for all finite families with candidates the serving protocols whose calibrated whole bill is at most C. Then each family is feasible, its familyCost equals the selected protocol’s bill, and it is ledger-admissible. Attainment is supplied through selection at this exact domain, not inferred from an arbitrary infimum.
-- source:
--   Sib v44 Theorems/Thm_APFB07a_protocol_binding.lean:31

import Definitions.Def_APFB07a_ProtocolBinding
import Mathlib.Tactic.Linarith

set_option autoImplicit false

open APFPaper1.Source

theorem APFB07a.familyCost_attained_of_A2 {D P R Record : Type*}
    (wholeResource : P → R) (calibration : R → NNReal) (maintained : P → Set Record)
    (sufficient : P → Set Record → D → Prop) (usesToRealize : P → D → Set Record → Prop)
    (C : ℝ) (realized : Finset D → P)
    (hA2 : APFB07a.A2Selection (Interface := Finset D) (Configuration := fun _ => P)
      (fun S p => APFB07a.protocolAdmissible wholeResource calibration maintained sufficient
        usesToRealize C S p)
      (fun _ p => APFB07a.protocolBill wholeResource calibration p) realized) (S : Finset D) :
    familyFeasible maintained sufficient usesToRealize S ∧
      familyCost wholeResource calibration maintained sufficient usesToRealize S =
        APFB07a.protocolBill wholeResource calibration (realized S) ∧
      familyAdmissible wholeResource calibration maintained sufficient usesToRealize C S := by sorry
