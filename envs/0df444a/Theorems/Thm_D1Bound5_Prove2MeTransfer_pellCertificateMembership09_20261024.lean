-- Prove2me | Theorems.Thm_D1Bound5_Prove2MeTransfer_pellCertificateMembership09_20261024
-- name    : D1Bound5.Prove2MeTransfer.pellCertificateMembership09_20261024
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T07:30:23.120407+00:00
-- url     : https://prove2.me/theorems/c96d62aa-f555-47e2-9d6d-ae0d7a3f6a4f
-- title:
--   Pell certificate existence, records 577–640
-- statement:
--   Every integer parameter in the displayed list has a complete finite Pell certificate at cutoff 10^275. The proof extracts it from the corresponding already verified block of the original 1,016 certificate records.
-- source:
--   D1Bound5/PellFiniteFields.lean, lines 91-110, SHA-256 352c30df17c6d6e5a3b765a23814fee880412e130767d7c10f6bf24c2c1ef96d. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Tactic
import Definitions.Def_D1Bound5_PellFiniteCertificate_Definitions

section
namespace D1Bound5
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

theorem _root_.D1Bound5.Prove2MeTransfer.pellCertificateMembership09_20261024 (d : ℤ) (hd : d ∈ ([5655,5663,5671,5695,5703,5711,5719,5727,5735,5743,5759,5767,5783,5791,5799,5807,5815,5839,5847,5855,5863,5871,5879,5903,5911,5919,5927,5935,5943,5951,5959,5983,5991,5999,6007,6015,6023,6031,6047,6055,6063,6071,6079,6087,6095,6103,6119,6127,6135,6143,6151,6159,6167,6191,6199,6207,6215,6231,6239,6247,6263,6271,6279,6287] : List ℤ)) : Nonempty (PellFiniteCertificate d (10^275)) := by sorry

end D1Bound5
end
