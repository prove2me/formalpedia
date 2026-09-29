-- Prove2me | Theorems.Thm_DecentralizedDistribution_FirstBest_example2_dual_allocation
-- name    : DecentralizedDistribution.FirstBest.example2_dual_allocation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T06:44:23.384907+00:00
-- url     : https://prove2.me/theorems/04784aa5-b1da-4112-a3cc-d1edc0d14879
-- title:
--   Example 2 — the dual allocation is (8, 8, 8, 0), and (0, 0, 0, 24) is also in the core
-- statement:
--   Take the system of Example 1 (four retailers, no warehouses, $r_n=10$, $v_n=5$, $t_{i,n}=1$, $\beta_{i,n}=1$) with local stocks $X=(2,2,2,0)$ and demands $\vec D=(0,0,0,10)$, so that $H_1=H_2=H_3=2$ and $E_4=10$. Then:
--   1. the total surplus from pooling is $W^*_{\mathcal N}([Z],\vec D)=6\times 4=24$;
--   2. dual prices of the shipping LP (6) exist, and every choice of them gives the dual allocation (8)
--   $$\alpha=(8,8,8,0);$$
--   3. the allocation $(0,0,0,24)$ is also in the core of SAG$([Z],\vec D)$.
--
--   The example shows that the core may contain allocations unrelated to dual prices.
--
--   **Formalization Note.** Retailers $1,\dots,4$ are indices $0,\dots,3$. The final sentence of the paper's example ("any allocation of the form $\alpha_n\le 8$ for $n=1,2,3$ and $\alpha_4=24-(\alpha_1+\alpha_2+\alpha_3)$ is in the core") is not formalized: it fails for negative $\alpha_n$, since the singleton coalitions force $\alpha_n\ge 0$.
-- source:
--   Anupindi, Bassok & Zemel, A General Framework for the Study of Decentralized Distribution Systems, MSOM 3(4) 2001, p. 359, Example 2

import Mathlib
import Definitions.Def_Supermodularity_Cooperative_Core
import Definitions.Def_DecentralizedDistribution_FirstBest_System
import Definitions.Def_DecentralizedDistribution_FirstBest_DualPrices

open Supermodularity.Cooperative

namespace DecentralizedDistribution.FirstBest

/-- Example 2 (p. 359). The system of Example 1 with stocks `X = (2, 2, 2, 0)` and demands
`D = (0, 0, 0, 10)`, so that `H_1 = H_2 = H_3 = 2` and `E_4 = 10`. Then `W*_𝒩 = 24`, dual prices
exist and every optimal dual gives the allocation (8) equal to `(8, 8, 8, 0)`, and the allocation
`(0, 0, 0, 24)` is also in the core of SAG([Z], D⃗). -/
theorem example2_dual_allocation (sys : System 4 0)
    (hr : ∀ n, sys.r n = 10) (hv : ∀ n, sys.v n = 5)
    (ht : ∀ i n, sys.t i n = 1) (hβ : ∀ i n, sys.β i n = 1)
    (Z : Profile 4 0) (hX : (fun n => (Z n).X) = ![2, 2, 2, 0])
    (D : Demand 4) (hD : D = ![0, 0, 0, 10]) :
    coalitionValue sys Finset.univ Z D = 24 ∧
    (∃ p, IsOptimalDual sys Z D p) ∧
    (∀ p, IsOptimalDual sys Z D p → dualAllocation Z D p = ![8, 8, 8, 0]) ∧
    (![0, 0, 0, 24] : Fin 4 → ℝ) ∈ Core Finset.univ (fun S => coalitionValue sys S Z D) := by sorry

end DecentralizedDistribution.FirstBest
