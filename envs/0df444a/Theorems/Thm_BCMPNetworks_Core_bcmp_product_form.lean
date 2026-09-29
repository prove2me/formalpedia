-- Prove2me | Theorems.Thm_BCMPNetworks_Core_bcmp_product_form
-- name    : BCMPNetworks.Core.bcmp_product_form
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T18:43:56.183072+00:00
-- url     : https://prove2.me/theorems/9df4b691-cb8e-4038-b123-9a659ec00a84
-- title:
--   BCMP theorem: product-form equilibrium of open, closed and mixed multiclass networks
-- statement:
--   Consider a network of $N$ service centers, each of type 1 (FCFS, exponential service common to all classes), 2 (processor sharing), 3 (infinite server) or 4 (preemptive-resume LCFS), with $R$ customer classes, class-switching routing $P$, subchains that may be open or closed, Coxian service times at type 2–4 centers, and arrival process (A) or (B), all satisfying the standing assumptions of §2 and §3.2. Let $e \ge 0$ solve the traffic equations, and let
--   $$\pi(S) = d(S)\,f_1(x_1)\,f_2(x_2)\cdots f_N(x_N)$$
--   be the product form of the paper (with $A_{irl} = \prod_{j<l} a_{irj}$). Then:
--
--   1. $\pi$ satisfies the global balance equations of the network;
--   2. assume, as the paper does, that the equilibrium distribution is unique (any two equilibrium distributions coincide). If $\sum_S \pi(S) = Z$ with $0 < Z$, then every equilibrium distribution $P$ is
--   $$P(S) = \frac{1}{Z}\, d(S)\,f_1(x_1)\cdots f_N(x_N),$$
--   i.e. $P = C\,d(S)\prod_i f_i(x_i)$ with normalizing constant $C = 1/Z$.
--
--   This is the BCMP theorem: the equilibrium distribution of an open, closed or mixed network of this class factorizes over the service centers.
--
--   **Formalization Note** The paper's $A_{irl} = \prod_{j=1}^{l} a_{irj}$ (p. 253) includes one factor too many: for exponential service ($u_{ir}=1$) it gives $A_{ir1} = a_{ir1} = 0$, so every $f_i$ of a type 2–4 center with a customer present vanishes and, for a closed network of such centers, no normalizing constant exists. The corrected $\prod_{j<l} a_{irj}$, the probability of reaching stage $l$, is used; §4.1's identity $1/\mu_{ir} = \sum_l A_{irl}/\mu_{irl}$ confirms this reading. The type-2 factor $1/m_{ikl}!$ is read $1/m_{irl}!$, and the $p_{ir}$ of the $d(S)$ sentence are the arrival probabilities $q_{ir}$. The paper's standing assumption that "the equilibrium probabilities exist and are unique" (p. 248) is split: uniqueness is a hypothesis, and existence is supplied by the summability of $\pi$ with $0<Z$. The type-1 service rate is constant, as in the displayed formula; the state-dependent rate of Condition 1 is not covered.
-- source:
--   Baskett, Chandy, Muntz, Palacios, Open, Closed, and Mixed Networks of Queues with Different Classes of Customers, J. ACM 22 (1975), pp. 253-254, Theorem (Section 3.2)

import Mathlib
import Definitions.Def_BCMPNetworks_Core_Network
import Definitions.Def_BCMPNetworks_Core_Dynamics
import Definitions.Def_BCMPNetworks_Core_ProductForm

namespace BCMPNetworks.Core

theorem bcmp_product_form {N R m : ℕ} (net : Network N R m)
    (hnet : net.IsValid) (e : Fin N → Fin R → ℝ) (he : ∀ i r, 0 ≤ e i r)
    (htraffic : net.TrafficEquations e) :
    GlobalBalance (net.productForm e) net.rate ∧
    ((∀ P Q : net.State → ℝ, net.IsEquilibrium P → net.IsEquilibrium Q → P = Q) →
      ∀ Z : ℝ, HasSum (net.productForm e) Z → 0 < Z →
        ∀ P : net.State → ℝ, net.IsEquilibrium P →
          ∀ S, P S = net.productForm e S / Z) := by sorry

end BCMPNetworks.Core
