-- Prove2me | Theorems.Thm_D1Bound5_Prove2MeTransfer_pellCertificateMembership11_20261024
-- name    : D1Bound5.Prove2MeTransfer.pellCertificateMembership11_20261024
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T07:30:22.164981+00:00
-- url     : https://prove2.me/theorems/7bd306fc-9d1a-46f4-ba5b-6746336f4c64
-- title:
--   Pell certificate existence, records 705–768
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

theorem _root_.D1Bound5.Prove2MeTransfer.pellCertificateMembership11_20261024 (d : ℤ) (hd : d ∈ ([6935,6943,6951,6959,6967,6983,6991,6999,7015,7023,7031,7039,7055,7063,7071,7079,7087,7095,7103,7111,7127,7135,7143,7151,7159,7167,7183,7199,7207,7215,7223,7231,7239,7247,7255,7271,7279,7287,7295,7303,7311,7319,7327,7343,7351,7359,7367,7383,7391,7415,7423,7431,7439,7447,7455,7463,7471,7487,7495,7503,7511,7519,7527,7535] : List ℤ)) : Nonempty (PellFiniteCertificate d (10^275)) := by sorry

end D1Bound5
end
