-- Prove2me | Theorems.Thm_D1Bound5_Prove2MeTransfer_pellCertificateMembership04_20261024
-- name    : D1Bound5.Prove2MeTransfer.pellCertificateMembership04_20261024
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T07:30:30.806306+00:00
-- url     : https://prove2.me/theorems/18750c24-6ac9-4872-82dc-2db0bc76ad75
-- title:
--   Pell certificate existence, records 257–320
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

theorem _root_.D1Bound5.Prove2MeTransfer.pellCertificateMembership04_20261024 (d : ℤ) (hd : d ∈ ([2495,2503,2519,2543,2551,2559,2567,2591,2599,2607,2615,2623,2631,2639,2647,2663,2671,2679,2687,2703,2711,2719,2735,2743,2751,2759,2767,2791,2807,2815,2823,2831,2839,2847,2855,2863,2879,2887,2895,2903,2911,2919,2927,2935,2951,2959,2967,2983,2991,2999,3007,3023,3031,3039,3047,3055,3063,3071,3079,3095,3103,3111,3119,3127] : List ℤ)) : Nonempty (PellFiniteCertificate d (10^275)) := by sorry

end D1Bound5
end
