-- Prove2me | Theorems.Thm_D1Bound5_Prove2MeTransfer_pellCertificateMembership03_20261024
-- name    : D1Bound5.Prove2MeTransfer.pellCertificateMembership03_20261024
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T07:31:31.862817+00:00
-- url     : https://prove2.me/theorems/4be074d6-f8e4-4918-bc25-8c9d1effdd92
-- title:
--   Pell certificate existence, records 193–256
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

theorem _root_.D1Bound5.Prove2MeTransfer.pellCertificateMembership03_20261024 (d : ℤ) (hd : d ∈ ([1871,1879,1887,1895,1903,1919,1927,1943,1951,1959,1967,1983,1991,1999,2015,2031,2039,2047,2055,2063,2071,2087,2095,2103,2111,2119,2127,2135,2143,2159,2167,2183,2191,2199,2207,2215,2231,2239,2247,2255,2263,2271,2279,2287,2311,2319,2327,2335,2343,2351,2359,2383,2391,2399,2407,2415,2423,2431,2447,2455,2463,2471,2479,2487] : List ℤ)) : Nonempty (PellFiniteCertificate d (10^275)) := by sorry

end D1Bound5
end
