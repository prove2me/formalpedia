-- Prove2me | Theorems.Thm_D1Bound5_Prove2MeTransfer_pellCertificateMembership08_20261024
-- name    : D1Bound5.Prove2MeTransfer.pellCertificateMembership08_20261024
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T07:30:22.990181+00:00
-- url     : https://prove2.me/theorems/71c87707-62b9-4e62-b88b-2cab71f76d21
-- title:
--   Pell certificate existence, records 513–576
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

theorem _root_.D1Bound5.Prove2MeTransfer.pellCertificateMembership08_20261024 (d : ℤ) (hd : d ∈ ([5023,5039,5055,5063,5071,5079,5087,5095,5111,5119,5127,5135,5143,5151,5159,5167,5183,5191,5199,5207,5215,5223,5231,5255,5263,5271,5279,5287,5295,5303,5311,5327,5335,5343,5351,5359,5367,5383,5399,5407,5423,5431,5447,5455,5471,5479,5487,5495,5503,5511,5519,5527,5543,5551,5559,5567,5583,5591,5599,5615,5623,5631,5639,5647] : List ℤ)) : Nonempty (PellFiniteCertificate d (10^275)) := by sorry

end D1Bound5
end
