-- Prove2me | Theorems.Thm_BellWilliams2001_ThresholdPolicy_workload_balance
-- name    : BellWilliams2001.ThresholdPolicy.workload_balance
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T05:51:51.766312+00:00
-- url     : https://prove2.me/theorems/f620b2c9-5792-56e2-a9d9-f8f4397d16ff
-- title:
--   The pooled workload balance for any allocation
-- statement:
--   The weighted diffusion-scaled queue length is the weighted centered input plus the idle-time terms of the two servers. The class 2 workload weight is the ratio of the two service rates at the flexible server. With this weight the split of service time at that server cancels, leaving its idle time as the only capacity term from that server.
-- source:
--   Bell and Williams (2001), https://doi.org/10.1214/aoap/1015345343, equation (97)

import Definitions.Def_BellWilliams2001_ThresholdPolicy_Workload

namespace BellWilliams2001.ThresholdPolicy

theorem workload_balance {Ω : Type*} [MeasurableSpace Ω] (M : SystemSequence Ω)
    (n : ℕ) (T : Allocation Ω) (ω : Ω) (t : ℝ) :
    M.workload n T ω t = M.serverTwoInput n T ω t + M.muR n 1 * M.Ihat n T ω t 1 := by sorry

end BellWilliams2001.ThresholdPolicy
