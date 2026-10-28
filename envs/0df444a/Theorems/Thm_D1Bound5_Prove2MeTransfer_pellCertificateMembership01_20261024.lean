-- Prove2me | Theorems.Thm_D1Bound5_Prove2MeTransfer_pellCertificateMembership01_20261024
-- name    : D1Bound5.Prove2MeTransfer.pellCertificateMembership01_20261024
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T07:30:34.089174+00:00
-- url     : https://prove2.me/theorems/b9cb8b5a-0fe3-4168-8836-fa7537746345
-- title:
--   Pell certificate existence, records 65–128
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

theorem _root_.D1Bound5.Prove2MeTransfer.pellCertificateMembership01_20261024 (d : ℤ) (hd : d ∈ ([615,623,631,647,655,663,671,679,687,695,703,719,727,743,751,759,767,791,799,807,815,823,831,839,863,871,879,887,895,903,911,919,935,943,951,959,967,983,991,1007,1015,1023,1031,1039,1047,1055,1063,1079,1087,1095,1103,1111,1119,1135,1151,1159,1167,1191,1199,1207,1223,1231,1239,1247] : List ℤ)) : Nonempty (PellFiniteCertificate d (10^275)) := by sorry

end D1Bound5
end
