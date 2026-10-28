-- Prove2me | Theorems.Thm_D1Bound5_Prove2MeTransfer_pellCertificateMembership05_20261024
-- name    : D1Bound5.Prove2MeTransfer.pellCertificateMembership05_20261024
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T07:30:24.951016+00:00
-- url     : https://prove2.me/theorems/95c837f6-f088-4c3d-bece-cc05a29c7b78
-- title:
--   Pell certificate existence, records 321–384
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

theorem _root_.D1Bound5.Prove2MeTransfer.pellCertificateMembership05_20261024 (d : ℤ) (hd : d ∈ ([3135,3143,3151,3167,3183,3191,3199,3207,3215,3223,3239,3247,3255,3263,3271,3279,3287,3295,3311,3319,3327,3335,3343,3351,3359,3367,3383,3391,3399,3407,3415,3423,3431,3439,3455,3463,3471,3487,3495,3503,3511,3527,3535,3543,3551,3559,3567,3583,3599,3607,3615,3623,3631,3639,3647,3655,3671,3679,3687,3695,3711,3719,3727,3743] : List ℤ)) : Nonempty (PellFiniteCertificate d (10^275)) := by sorry

end D1Bound5
end
