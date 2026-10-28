-- Prove2me | Theorems.Thm_D1Bound5_Prove2MeTransfer_pellCertificateMembership15_20261024
-- name    : D1Bound5.Prove2MeTransfer.pellCertificateMembership15_20261024
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T07:30:26.664985+00:00
-- url     : https://prove2.me/theorems/7e4f1134-050e-4c7b-9d4a-c4b5206481b8
-- title:
--   Pell certificate existence, records 961–1016
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

theorem _root_.D1Bound5.Prove2MeTransfer.pellCertificateMembership15_20261024 (d : ℤ) (hd : d ∈ ([9447,9455,9463,9471,9479,9487,9503,9511,9519,9527,9535,9543,9551,9591,9599,9607,9615,9623,9631,9647,9655,9663,9671,9679,9687,9695,9703,9719,9727,9735,9743,9759,9767,9791,9799,9807,9815,9823,9831,9839,9847,9863,9871,9879,9887,9895,9903,9911,9919,9935,9943,9951,9959,9967,9983,9991] : List ℤ)) : Nonempty (PellFiniteCertificate d (10^275)) := by sorry

end D1Bound5
end
