-- Prove2me | Theorems.Thm_FamousTheorems_tendsto_tsum_powerseries_nhdswithin_stolzcone
-- name    : FamousTheorems.tendsto_tsum_powerseries_nhdswithin_stolzcone
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-22T13:01:15.848654+00:00
-- url     : https://prove2.me/theorems/b0313107-53d4-4e93-af77-a4efa0300c9f
-- title:
--   Abel's theorem
-- statement:
--   **Abel's theorem.** If a power series converges at a boundary point of its disc of convergence, its sum approaches that value as the variable tends to the point within a Stolz cone. Convergence at the boundary, which need not be absolute, still controls the radial limit — provided the approach is non-tangential, which is exactly what the Stolz cone enforces. The theorem is what justifies summing conditionally convergent series by taking limits of power series, giving $\log 2 = 1 - 1/2 + 1/3 - \cdots$ and Leibniz's $\pi/4 = 1 - 1/3 + 1/5 - \cdots$ from the expansions of $\log(1+x)$ and $\arctan x$. **Formalization note.** `stolzCone` is the non-tangential approach region at the boundary point. The result is Mathlib's `Complex.tendsto_tsum_powerSeries_nhdsWithin_stolzCone`.
-- source:
--   Listed in Mathlib's curated theorem manifests; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem tendsto_tsum_powerseries_nhdswithin_stolzcone :
    ∀ {f : ℕ → ℂ} {l : ℂ}, 
    Tendsto (fun n => ∑ i ∈ Finset.range n, f i) atTop (𝓝 l) → 
    ∀ {s : ℝ}, 0 < s → Tendsto (fun z => ∑' (n : ℕ), f n * z ^ n) (𝓝[Complex.stolzCone s] 1) (𝓝 l) := by sorry

end FamousTheorems
