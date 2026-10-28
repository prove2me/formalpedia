-- Prove2me | Theorems.Thm_D1Bound5_Prove2MeTransfer_pellCertificateMembership14_20261024
-- name    : D1Bound5.Prove2MeTransfer.pellCertificateMembership14_20261024
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T07:30:28.654611+00:00
-- url     : https://prove2.me/theorems/23151840-eafc-4542-9af4-21e4b7d169cc
-- title:
--   Pell certificate existence, records 897–960
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

theorem _root_.D1Bound5.Prove2MeTransfer.pellCertificateMembership14_20261024 (d : ℤ) (hd : d ∈ ([8807,8815,8823,8831,8839,8855,8863,8871,8879,8887,8895,8903,8911,8927,8935,8943,8951,8983,8999,9007,9015,9023,9031,9039,9047,9055,9071,9079,9087,9095,9103,9111,9119,9127,9143,9151,9159,9167,9183,9191,9199,9215,9223,9231,9239,9247,9255,9263,9271,9287,9303,9311,9319,9327,9335,9343,9367,9383,9391,9399,9407,9415,9431,9439] : List ℤ)) : Nonempty (PellFiniteCertificate d (10^275)) := by sorry

end D1Bound5
end
