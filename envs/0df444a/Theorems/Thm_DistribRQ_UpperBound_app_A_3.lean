-- Prove2me | Theorems.Thm_DistribRQ_UpperBound_app_A_3
-- name    : DistribRQ.UpperBound.app_A_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:23:22.077991+00:00
-- url     : https://prove2.me/theorems/54056b13-aa80-4400-b1b8-736c73df4241
-- title:
--   App. A (3), p. A2 — per-retailer bound: Γ̂ᵢ(IPᵢ(t)) ≤ max{Gᵢ(wᵢ), Cᵢ} or max{Gᵢ(IL0(t) − Σ_{j≠i}(rⱼ+Qⱼ)), Gᵢ(wᵢ), Cᵢ}
-- statement:
--   Consider the one-warehouse, $N$-retailer system under a modified echelon $(r,Q)$ policy, with the single-stage costs $G_i$, $C_i=C_i(r_i,Q_i)$ and $G_i(w_i)=\sup_{r_i<z\le r_i+Q_i}G_i(z)$ of the module `DistribRQ.UpperBound.Model`. Let $c=(c_i)$ be an admissible family of charges: $c_i(z)\le\max\{G_i(z),C_i\}$ when $z>r_i$, and $c_i(z)\le G_i(z)$ when $z\le r_i$. Let $x$ be the warehouse echelon inventory level and $z$ a feasible vector of retailer inventory positions at $x$ (each $z_j\le r_j+Q_j$, $\sum_jz_j\le x$, and $z_i>r_i$ for all $i$ if $\sum_jz_j<x$). Then for every retailer $i$,
--   $$
--   c_i(z_i)\le\begin{cases}\max\{G_i(w_i),C_i(r_i,Q_i)\} & \text{if } x-\sum_{j\ne i}(r_j+Q_j)>r_i,\\[2pt] \max\Big\{G_i\big(x-\sum_{j\ne i}(r_j+Q_j)\big),\,G_i(w_i),\,C_i(r_i,Q_i)\Big\} & \text{otherwise.}\end{cases}
--   $$
--
--   This is the per-retailer bound from which Lemma 3 is assembled: it bounds retailer $i$'s cost rate in terms of the warehouse's echelon level rather than its own inventory position.
--
--   **Formalization Note** $\hat\Gamma_i(IP_i(t))$ of the page is the charge $c_i(z_i)$ at the feasible state $z$; $IL_0(t)$ is $x$. The page's equality $\hat\Gamma_i=G_i$ for $IP_i\le r_i$ is weakened to "$\le$" in the admissibility hypothesis, so the statement covers the page's charge.
-- source:
--   Zhu, Chen, Hu & Yang, A simple heuristic policy for stochastic distribution inventory systems with fixed shipment costs, SSRN 2921743 (2020-09-08 copy), pp. A1–A2 (PDF 20–21), Online Appendix A, proof of Lemma 3, App. A (3)

import Mathlib
import Definitions.Def_DistribRQ_UpperBound_Model

open MeasureTheory ProbabilityTheory

namespace DistribRQ.UpperBound

/-- App. A (3), p. A2 (Zhu, Chen, Hu & Yang, SSRN 2921743): for an admissible charge `c` and a
feasible vector `z` of retailer inventory positions at warehouse echelon level `x`, the charge
of retailer `i` is at most the own-retailer term of `Γ̄ᵢ(x)`. -/
theorem app_A_3 {N : ℕ} (P : Primitives N) (π : Policy N) (c : Fin N → ℝ → ℝ) (hc : AdmissibleCharge P π c) (x : ℝ) (z : Fin N → ℝ) (hz : z ∈ Feasible π x) (i : Fin N) : c i (z i) ≤ GammaBarOwn P π i x := by sorry

end DistribRQ.UpperBound
