-- Prove2me | Theorems.Thm_BCMPNetworks_Core_independent_balance_imp_global_balance
-- name    : BCMPNetworks.Core.independent_balance_imp_global_balance
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T18:42:38.173991+00:00
-- url     : https://prove2.me/theorems/4b031372-935e-4acc-b2ba-da94c53600b0
-- title:
--   Section 3.1 — independent balance implies global balance
-- statement:
--   Let a BCMP network satisfy the standing assumptions of §2 and §3.2 (nonnegative substochastic routing that stays inside subchains, closed subchains with no arrivals and no departures, positive service rates, continuation probabilities in $[0,1]$ vanishing at the last stage). If a function $\pi$ on the state space satisfies the independent balance equations, then it satisfies the global balance equations:
--   $$\pi(S)\sum_{S'} q(S,S') = \sum_{S'} \pi(S')\,q(S',S) \quad\text{for every state } S.$$
--
--   Each global balance equation is the sum, over all labels, of independent balance equations; this is why the product form can be verified label by label.
--
--   **Formalization Note** The standing assumptions are needed so that every event with nonzero rate from a feasible state leads to a feasible state (in particular, closed subchains keep their populations).
-- source:
--   Baskett, Chandy, Muntz, Palacios, Open, Closed, and Mixed Networks of Queues with Different Classes of Customers, J. ACM 22 (1975), p. 252, Section 3.1; restated p. 253

import Mathlib
import Definitions.Def_BCMPNetworks_Core_Network
import Definitions.Def_BCMPNetworks_Core_Dynamics
import Definitions.Def_BCMPNetworks_Core_IndependentBalance

namespace BCMPNetworks.Core

theorem independent_balance_imp_global_balance {N R m : ℕ} (net : Network N R m)
    (hnet : net.IsValid) (π : net.State → ℝ) (hπ : net.IndependentBalance π) :
    GlobalBalance π net.rate := by sorry

end BCMPNetworks.Core
