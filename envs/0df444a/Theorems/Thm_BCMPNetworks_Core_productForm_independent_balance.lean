-- Prove2me | Theorems.Thm_BCMPNetworks_Core_productForm_independent_balance
-- name    : BCMPNetworks.Core.productForm_independent_balance
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T18:43:27.932697+00:00
-- url     : https://prove2.me/theorems/54b1421e-f94b-4c1c-9538-e2a4fd7e3e77
-- title:
--   Section 3.2 — the product form satisfies the independent balance equations
-- statement:
--   Let a BCMP network satisfy the standing assumptions of §2 and §3.2, and let $e = (e_{ir})$ be any nonnegative solution of the traffic equations
--   $$\sum_{(i,r)} e_{ir}\,p_{i,r;j,s} + q_{js} = e_{js}.$$
--   Then the product form $\pi(S) = d(S)\,f_1(x_1)\cdots f_N(x_N)$ satisfies the independent balance equations, for every state and every label (each stage of a type 2–4 center, each type-1 center, and the outside world of each subchain).
--
--   This is the step by which the paper proves its THEOREM: for every label the independent balance equation reduces to the traffic equations.
--
--   **Formalization Note** $A_{irl} = \prod_{j<l} a_{irj}$ is the corrected form of the paper's $A_{irl}$ (see the network definition). Any nonnegative solution $e$ is allowed; the paper's $e$ (unique for open subchains, unique up to a factor for closed ones) is a special case.
-- source:
--   Baskett, Chandy, Muntz, Palacios, Open, Closed, and Mixed Networks of Queues with Different Classes of Customers, J. ACM 22 (1975), p. 254, Section 3.2 (proof of the THEOREM)

import Mathlib
import Definitions.Def_BCMPNetworks_Core_Network
import Definitions.Def_BCMPNetworks_Core_Dynamics
import Definitions.Def_BCMPNetworks_Core_ProductForm
import Definitions.Def_BCMPNetworks_Core_IndependentBalance

namespace BCMPNetworks.Core

theorem productForm_independent_balance {N R m : ℕ} (net : Network N R m)
    (hnet : net.IsValid) (e : Fin N → Fin R → ℝ) (he : ∀ i r, 0 ≤ e i r)
    (htraffic : net.TrafficEquations e) :
    net.IndependentBalance (net.productForm e) := by sorry

end BCMPNetworks.Core
