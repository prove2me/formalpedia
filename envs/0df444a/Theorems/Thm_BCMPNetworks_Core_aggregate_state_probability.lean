-- Prove2me | Theorems.Thm_BCMPNetworks_Core_aggregate_state_probability
-- name    : BCMPNetworks.Core.aggregate_state_probability
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T18:45:30.222095+00:00
-- url     : https://prove2.me/theorems/9f294ec8-b681-4501-b0c7-cbdd8d11a8d4
-- title:
--   Section 4.1 — aggregate-state probabilities $C\,d(S)\,g_1(y_1)\cdots g_N(y_N)$
-- statement:
--   Under the hypotheses of the BCMP theorem (standing assumptions, $e \ge 0$ solving the traffic equations, uniqueness of the equilibrium distribution, and $\sum_S \pi(S) = Z > 0$), let $P$ be the equilibrium distribution and $S_0$ a state whose class counts at the centers are $(y_1,\dots,y_N)$, $y_i = (n_{i1},\dots,n_{iR})$. Then the equilibrium probability of the **aggregate state** $(y_1,\dots,y_N)$, i.e. of the set of states with these class counts, is
--   $$P\big(S = (y_1,\dots,y_N)\big) = \frac{1}{Z}\,d(S_0)\,g_1(y_1)\,g_2(y_2)\cdots g_N(y_N).$$
--
--   The value $d(S_0)$ depends only on the class counts, so the formula is $C\,d(S)\,g_1(y_1)\cdots g_N(y_N)$ of the paper with $C = 1/Z$. It reduces the computation of the normalizing constant and marginals to class counts.
--
--   **Formalization Note** The statement requires a feasible state $S_0$ with the given counts, so that the aggregate state is nonempty. The probability is stated as a `HasSum` of $P$ over the set of states with the counts of $S_0$.
-- source:
--   Baskett, Chandy, Muntz, Palacios, Open, Closed, and Mixed Networks of Queues with Different Classes of Customers, J. ACM 22 (1975), p. 254, Section 4.1

import Mathlib
import Definitions.Def_BCMPNetworks_Core_Network
import Definitions.Def_BCMPNetworks_Core_Dynamics
import Definitions.Def_BCMPNetworks_Core_ProductForm
import Definitions.Def_BCMPNetworks_Core_Aggregate

namespace BCMPNetworks.Core

theorem aggregate_state_probability {N R m : ℕ} (net : Network N R m)
    (hnet : net.IsValid) (e : Fin N → Fin R → ℝ) (he : ∀ i r, 0 ≤ e i r)
    (htraffic : net.TrafficEquations e)
    (huniq : ∀ P Q : net.State → ℝ, net.IsEquilibrium P → net.IsEquilibrium Q → P = Q)
    (Z : ℝ) (hZ : HasSum (net.productForm e) Z) (hZpos : 0 < Z)
    (P : net.State → ℝ) (hP : net.IsEquilibrium P) (S₀ : net.State) :
    HasSum
      (fun S : {S : net.State // ∀ i r, (S.1 i).count r = (S₀.1 i).count r} => P S.1)
      (net.d S₀.1 * (∏ i, net.g e i (fun r => (S₀.1 i).count r)) / Z) := by sorry

end BCMPNetworks.Core
