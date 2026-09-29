-- Prove2me | Theorems.Thm_DecentralizedDistribution_FirstBest_example1_transfer_price_not_in_core
-- name    : DecentralizedDistribution.FirstBest.example1_transfer_price_not_in_core
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T06:39:18.456425+00:00
-- url     : https://prove2.me/theorems/1269a92a-2e44-449c-a99f-7b655252f059
-- title:
--   Example 1 — the transfer-price allocation (0, 0, 16, 0) is not in the core
-- statement:
--   Consider four retailers and no warehouses with $r_n=10$, $v_n=5$ for every $n$, $t_{i,n}=1$ and $\beta_{i,n}=1$ for every arc, so that every shipment of excess supply to excess demand earns $10-5-1=4$ per unit. Take local stocks $X=(3,1,0,0)$ and demands $\vec D=(0,0,5,2)$, so that $H_1=3$, $H_2=1$, $E_3=5$, $E_4=2$ and all other residuals vanish. Then
--   $$W^*_{\mathcal N}([Z],\vec D)=16,\qquad W^*_{\{1,4\}}([Z],\vec D)=8,$$
--   and the allocation $(0,0,16,0)$, which gives the whole excess profit to the retailers whose residual demand is served, is not in the core of SAG$([Z],\vec D)$: it violates the core constraint (7a) for the coalition $\{1,4\}$.
--
--   The example shows that allocations by predetermined transfer prices need not lie in the core.
--
--   **Formalization Note.** Retailers $1,\dots,4$ are indices $0,\dots,3$, so $\{1,4\}$ is `{0, 3}`. The costs $c_n$ are left arbitrary (they do not enter $W^*$). The paper gives only the residuals; the stocks and demands above are one realization producing them.
-- source:
--   Anupindi, Bassok & Zemel, A General Framework for the Study of Decentralized Distribution Systems, MSOM 3(4) 2001, p. 358, Example 1

import Mathlib
import Definitions.Def_Supermodularity_Cooperative_Core
import Definitions.Def_DecentralizedDistribution_FirstBest_System

open Supermodularity.Cooperative

namespace DecentralizedDistribution.FirstBest

/-- Example 1 (p. 358). Four retailers, no warehouses, `r_n = 10`, `v_n = 5`, `t_{i,n} = 1`,
`β_{i,n} = 1`; stocks `X = (3, 1, 0, 0)` and demands `D = (0, 0, 5, 2)`, so that
`H_1 = 3, H_2 = 1, E_3 = 5, E_4 = 2` (all other residuals zero). Then `W*_𝒩 = 16`, the coalition
`{1, 4}` (indices `0, 3`) has `W*_{{1,4}} = 8`, and the transfer-price allocation `(0, 0, 16, 0)`
is not in the core of SAG([Z], D⃗). -/
theorem example1_transfer_price_not_in_core (sys : System 4 0)
    (hr : ∀ n, sys.r n = 10) (hv : ∀ n, sys.v n = 5)
    (ht : ∀ i n, sys.t i n = 1) (hβ : ∀ i n, sys.β i n = 1)
    (Z : Profile 4 0) (hX : (fun n => (Z n).X) = ![3, 1, 0, 0])
    (D : Demand 4) (hD : D = ![0, 0, 5, 2]) :
    coalitionValue sys Finset.univ Z D = 16 ∧
    coalitionValue sys {0, 3} Z D = 8 ∧
    (![0, 0, 16, 0] : Fin 4 → ℝ) ∉ Core Finset.univ (fun S => coalitionValue sys S Z D) := by sorry

end DecentralizedDistribution.FirstBest
