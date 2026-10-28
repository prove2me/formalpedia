-- Prove2me | Theorems.Thm_D1Bound5_Prove2MeTransfer_pellCertificateMembership02_20261024
-- name    : D1Bound5.Prove2MeTransfer.pellCertificateMembership02_20261024
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T07:30:21.981979+00:00
-- url     : https://prove2.me/theorems/b4e40206-d56b-4a7c-9df1-66c55555376c
-- title:
--   Pell certificate existence, records 129–192
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

theorem _root_.D1Bound5.Prove2MeTransfer.pellCertificateMembership02_20261024 (d : ℤ) (hd : d ∈ ([1255,1263,1271,1279,1295,1303,1311,1319,1327,1335,1343,1351,1367,1383,1391,1399,1407,1415,1423,1439,1447,1455,1463,1471,1479,1487,1495,1511,1527,1535,1543,1551,1559,1567,1583,1591,1599,1607,1615,1623,1631,1639,1655,1663,1671,1679,1687,1695,1703,1711,1727,1735,1743,1751,1759,1767,1783,1799,1807,1823,1831,1839,1847,1855] : List ℤ)) : Nonempty (PellFiniteCertificate d (10^275)) := by sorry

end D1Bound5
end
