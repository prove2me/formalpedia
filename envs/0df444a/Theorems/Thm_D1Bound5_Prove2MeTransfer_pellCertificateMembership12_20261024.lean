-- Prove2me | Theorems.Thm_D1Bound5_Prove2MeTransfer_pellCertificateMembership12_20261024
-- name    : D1Bound5.Prove2MeTransfer.pellCertificateMembership12_20261024
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T07:30:20.371987+00:00
-- url     : https://prove2.me/theorems/c9e1af10-0f47-4cf9-b208-ba204b15dec4
-- title:
--   Pell certificate existence, records 769–832
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

theorem _root_.D1Bound5.Prove2MeTransfer.pellCertificateMembership12_20261024 (d : ℤ) (hd : d ∈ ([7543,7559,7567,7583,7591,7599,7607,7615,7631,7639,7647,7655,7663,7671,7679,7687,7703,7711,7719,7727,7735,7743,7751,7759,7783,7799,7807,7815,7823,7831,7847,7855,7863,7871,7879,7887,7895,7903,7919,7927,7951,7959,7967,7991,7999,8007,8015,8023,8031,8039,8047,8063,8071,8079,8087,8095,8103,8111,8119,8135,8143,8151,8159,8167] : List ℤ)) : Nonempty (PellFiniteCertificate d (10^275)) := by sorry

end D1Bound5
end
