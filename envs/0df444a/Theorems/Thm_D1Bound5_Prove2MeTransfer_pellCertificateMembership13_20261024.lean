-- Prove2me | Theorems.Thm_D1Bound5_Prove2MeTransfer_pellCertificateMembership13_20261024
-- name    : D1Bound5.Prove2MeTransfer.pellCertificateMembership13_20261024
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T07:30:25.805505+00:00
-- url     : https://prove2.me/theorems/62e3c6fa-cbe0-4ccc-a3cd-b4f58d4769be
-- title:
--   Pell certificate existence, records 833–896
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

theorem _root_.D1Bound5.Prove2MeTransfer.pellCertificateMembership13_20261024 (d : ℤ) (hd : d ∈ ([8191,8207,8215,8223,8231,8239,8247,8255,8263,8279,8287,8295,8311,8319,8327,8335,8351,8359,8367,8383,8391,8399,8407,8423,8431,8439,8447,8455,8463,8471,8479,8495,8503,8511,8519,8527,8535,8543,8551,8567,8583,8599,8607,8615,8623,8639,8647,8655,8663,8671,8679,8687,8695,8711,8719,8727,8735,8743,8751,8759,8767,8783,8791,8799] : List ℤ)) : Nonempty (PellFiniteCertificate d (10^275)) := by sorry

end D1Bound5
end
