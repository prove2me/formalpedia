-- Prove2me | Theorems.Thm_D1Bound5_Prove2MeTransfer_pellCertificateMembership06_20261024
-- name    : D1Bound5.Prove2MeTransfer.pellCertificateMembership06_20261024
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T07:30:25.443299+00:00
-- url     : https://prove2.me/theorems/e731abe1-6269-4942-9227-b8243b11190c
-- title:
--   Pell certificate existence, records 385–448
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

theorem _root_.D1Bound5.Prove2MeTransfer.pellCertificateMembership06_20261024 (d : ℤ) (hd : d ∈ ([3759,3767,3783,3791,3799,3815,3823,3831,3839,3847,3855,3863,3895,3903,3911,3919,3927,3935,3943,3959,3967,3983,3991,3999,4007,4015,4031,4039,4047,4055,4063,4071,4079,4087,4103,4111,4119,4127,4135,4143,4151,4159,4183,4191,4199,4207,4215,4223,4231,4247,4255,4271,4279,4287,4295,4303,4319,4327,4343,4351,4359,4367,4391,4399] : List ℤ)) : Nonempty (PellFiniteCertificate d (10^275)) := by sorry

end D1Bound5
end
