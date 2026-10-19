-- Prove2me | Theorems.Thm_DistribRQ_UpperBound_lemma_3
-- name    : DistribRQ.UpperBound.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:23:26.521771+00:00
-- url     : https://prove2.me/theorems/67b2fb34-1041-4b1e-b2e9-dc908de05e4b
-- title:
--   Lemma 3, pp. 11–12 — the retailers' cost rate is at most Γ̄(IL0(t)) = maxᵢ Γ̄ᵢ(IL0(t))
-- statement:
--   Consider the one-warehouse, $N$-retailer system ($N\ge1$) under a modified echelon $(r,Q)$ policy, with the envelope $\bar\Gamma=\max_i\bar\Gamma_i$ of the module `DistribRQ.UpperBound.Model`:
--   $$
--   \bar\Gamma_i(x)=\sum_{j\ne i}\max\{G_j(w_j),C_j(r_j,Q_j)\}+\begin{cases}\max\{G_i(w_i),C_i(r_i,Q_i)\} & \text{if } x-\sum_{j\ne i}(r_j+Q_j)>r_i,\\ \max\big\{G_i\big(x-\sum_{j\ne i}(r_j+Q_j)\big),G_i(w_i),C_i(r_i,Q_i)\big\} & \text{otherwise,}\end{cases}
--   $$
--   where $G_i(w_i)=\sup_{r_i<z\le r_i+Q_i}G_i(z)$. Let $c=(c_i)$ be an admissible family of retailer charges and let $z$ be a feasible vector of retailer inventory positions at warehouse echelon inventory level $x$. Then
--   $$
--   \sum_{i=1}^Nc_i(z_i)\le\bar\Gamma(x)=\max_{1\le i\le N}\bar\Gamma_i(x).
--   $$
--
--   In the paper this says that, at any time in a non-empty cycle, the expected cost rate of all retailers, excluding the fixed costs of Type II irregular shipments, is at most $\bar\Gamma(IL_0(t))$, a function of the warehouse echelon level alone. It is the step that turns the $N$-retailer problem into a single-stage bound at the warehouse.
--
--   **Formalization Note** "For any time $t$ in a non-empty cycle" is replaced by "for every feasible state" (the invariants of p. A1), which is more general. $\hat\Gamma(IL_0(t))=\sum_i\hat\Gamma_i(IP_i(t))$ is the sum of the charges. $G_i(w_i)$ is a supremum because the $\arg\max$ over $(r_i,r_i+Q_i]$ need not be attained.
-- source:
--   Zhu, Chen, Hu & Yang, A simple heuristic policy for stochastic distribution inventory systems with fixed shipment costs, SSRN 2921743 (2020-09-08 copy), pp. 11–12, Lemma 3, (4); proof pp. A1–A3

import Mathlib
import Definitions.Def_DistribRQ_UpperBound_Model

open MeasureTheory ProbabilityTheory

namespace DistribRQ.UpperBound

/-- Lemma 3, pp. 11–12 (Zhu, Chen, Hu & Yang, SSRN 2921743): at every feasible state, the total
retailer charge (Type II fixed costs excluded) is at most `Γ̄(IL₀) = maxᵢ Γ̄ᵢ(IL₀)`. -/
theorem lemma_3 {N : ℕ} [NeZero N] (P : Primitives N) (π : Policy N) (c : Fin N → ℝ → ℝ) (hc : AdmissibleCharge P π c) (x : ℝ) (z : Fin N → ℝ) (hz : z ∈ Feasible π x) : ∑ i, c i (z i) ≤ GammaBar P π x := by sorry

end DistribRQ.UpperBound
