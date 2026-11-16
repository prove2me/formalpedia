-- Prove2me | Theorems.Thm_APFPaper1_RecordLedger_bill_eq_sum
-- name    : APFPaper1.RecordLedger.bill_eq_sum
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-15T20:10:33.226636+00:00
-- url     : https://prove2.me/theorems/f866ff51-eac4-49a0-865b-18ff4f170a8e
-- title:
--   A record-ledger bill equals its kept-record cost sum
-- statement:
--   For the defined RecordLedger representation, the real-valued calibrated bill of a protocol is the sum of the costs of its kept records.
--
--   Publication scope: needsFin containment also holds in its empty fallback case. Equality with needs requires a sufficient set inside an actually finite kept set. Theorems of this representation do not prove its physical universality or availability.
-- source:
--   ['C:/Users/brook/My Drive/__APF Library/Artifacts_2026-11-15_session/astra/sib_v66_publication/source/Theorems/Thm_APFPaper1_RecordLedger_laws.lean:33 (source SHA256 2a39a7656440238ff3229c3e16cdfa9575022faf7490a9d1758f921e122dff19; APFPaper1.RecordLedger.bill_eq_sum)', 'C:/Users/brook/My Drive/__APF Library/Artifacts_2026-11-15_session/astra/sib_v66_publication/reviews/rv2_v66_v22_review.json (SHA256 365ce42aeeada41fa76b7443fe2b5af6017c7fdeb2bb28169266b6dbba622948; modules[Theorems.Thm_APFPaper1_RecordLedger_laws].declarations[APFPaper1.RecordLedger.bill_eq_sum])']

import Definitions.Def_APFPaper1_RecordLedger
import Mathlib.Data.NNReal.Basic

set_option autoImplicit false

namespace APFPaper1.RecordLedger
end APFPaper1.RecordLedger
open APFPaper1
open APFPaper1.RecordLedger
variable {D P Record : Type*} (L : RecordLedger D P Record)

theorem APFPaper1.RecordLedger.bill_eq_sum (p : P) :
    ((L.calibration (L.wholeResource p) : NNReal) : ℝ) = ∑ r ∈ L.kept p, ((L.cost r : NNReal) : ℝ) := by sorry
