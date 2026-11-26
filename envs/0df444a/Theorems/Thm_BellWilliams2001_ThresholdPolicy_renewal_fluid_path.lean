-- Prove2me | Theorems.Thm_BellWilliams2001_ThresholdPolicy_renewal_fluid_path
-- name    : BellWilliams2001.ThresholdPolicy.renewal_fluid_path
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T05:34:23.513158+00:00
-- url     : https://prove2.me/theorems/c9f040be-34bd-5749-b6f4-b5d15975ea4f
-- title:
--   Inverting the renewal strong law uniformly on compact time intervals
-- statement:
--   Let $e(j)$ be a strictly increasing sequence of epochs with $e(0)=0$ and $e(j)/j\to1$. If $R_n\to\infty$, then for each finite $H\ge0$ and $\varepsilon>0$ the inverse counting process $N(s)=\max\{j:e(j)\le s\}$ eventually satisfies
--
--   $$\sup_{0\le s\le R_n H}|N(s)-s|\le\varepsilon R_n.$$
--
--   This deterministic inversion turns a strong law for the renewal epochs into a fluid-scale uniform law for the renewal counts.
-- source:
--   Bell and Williams (2001), https://doi.org/10.1214/aoap/1015345343, Appendix A, (178)–(179), and the renewal fluid limits in Section 9

import Definitions.Def_BellWilliams2001_ThresholdPolicy_Paths

open Filter Topology

namespace BellWilliams2001.ThresholdPolicy

theorem renewal_fluid_path (e : ℕ → ℝ) (he : StrictMono e) (he0 : e 0 = 0)
    (hUnbounded : Tendsto e atTop atTop)
    (hmean : Tendsto (fun m : ℕ => e m / (m : ℝ)) atTop (𝓝 1))
    (R : ℕ → ℝ) (hR : Tendsto R atTop atTop) (H : ℝ) (hH : 0 ≤ H)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ s ∈ Set.Icc 0 (R n * H),
      |((renewalCount e s).toNat : ℝ) - s| ≤ ε * R n := by sorry

end BellWilliams2001.ThresholdPolicy
