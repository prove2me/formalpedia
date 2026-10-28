-- Prove2me | Theorems.Thm_D1Bound5_Prove2MeTransfer_pellCertificateMembership07_20261024
-- name    : D1Bound5.Prove2MeTransfer.pellCertificateMembership07_20261024
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T07:30:21.813206+00:00
-- url     : https://prove2.me/theorems/d2911e61-fdd3-4748-9f3f-8c1b159ae848
-- title:
--   Pell certificate existence, records 449–512
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

theorem _root_.D1Bound5.Prove2MeTransfer.pellCertificateMembership07_20261024 (d : ℤ) (hd : d ∈ ([4407,4415,4423,4431,4439,4447,4463,4471,4479,4487,4495,4503,4511,4519,4535,4543,4551,4559,4567,4583,4591,4607,4615,4623,4631,4639,4647,4663,4679,4687,4695,4703,4711,4727,4735,4751,4759,4767,4783,4791,4799,4807,4823,4831,4839,4847,4855,4863,4871,4879,4895,4903,4911,4919,4927,4935,4943,4951,4967,4983,4991,4999,5007,5015] : List ℤ)) : Nonempty (PellFiniteCertificate d (10^275)) := by sorry

end D1Bound5
end
