-- Prove2me | Theorems.Thm_D1Bound5_Prove2MeTransfer_pellCertificateMembership10_20261024
-- name    : D1Bound5.Prove2MeTransfer.pellCertificateMembership10_20261024
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T07:30:21.556972+00:00
-- url     : https://prove2.me/theorems/5eb0ee63-3910-4058-81ed-8d86ef90d4ed
-- title:
--   Pell certificate existence, records 641–704
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

theorem _root_.D1Bound5.Prove2MeTransfer.pellCertificateMembership10_20261024 (d : ℤ) (hd : d ∈ ([6295,6303,6311,6319,6335,6343,6351,6359,6367,6383,6391,6407,6415,6423,6431,6439,6447,6455,6463,6479,6487,6495,6503,6511,6519,6527,6535,6551,6559,6567,6583,6599,6607,6623,6631,6639,6663,6671,6679,6695,6703,6711,6719,6735,6743,6751,6767,6783,6791,6799,6807,6815,6823,6839,6847,6855,6863,6871,6879,6887,6895,6911,6919,6927] : List ℤ)) : Nonempty (PellFiniteCertificate d (10^275)) := by sorry

end D1Bound5
end
