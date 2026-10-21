-- Prove2me | Theorems.Thm_DistribRQ_UpperBound_app_A_9
-- name    : DistribRQ.UpperBound.app_A_9
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T04:23:43.419661+00:00
-- url     : https://prove2.me/theorems/ef802423-8df2-4c35-8845-7b0b8131352f
-- title:
--   App. A (9), p. A4 — Γ0(IP0(t)) ≤ Λ0(IP0(t)) + Σᵢ Cᵢ(rᵢ,Qᵢ)
-- statement:
--   Consider the one-warehouse, $N$-retailer system ($N\ge1$) under a modified echelon $(r,Q)$ policy, with $\kappa$ a Markov kernel concentrated on the feasible retailer states and $c$ an admissible family of measurable, nonnegative charges, as in App. A (8). Let $D_0\sim\mathrm{Poisson}(\lambda_0L_0)$ be the system demand over a warehouse lead time, $\hat\Gamma(x)=\int\sum_ic_i(z_i)\,\kappa(x)(dz)$, and
--   $$
--   \Gamma_0(y)=\mathbb E\big[h_0(y-D_0)\big]+\mathbb E\big[\hat\Gamma(y-D_0)\big]
--   $$
--   the expected cost rate of all installations when the warehouse inventory position is $y$ (fixed costs at the warehouse and Type II fixed costs at the retailers excluded). Then for every $y$,
--   $$
--   \Gamma_0(y)\le\Lambda_0(y)+\sum_{i=1}^NC_i(r_i,Q_i),\qquad \Lambda_0(y)=\mathbb E\big[h_0(y-D_0)+\hat G(y-D_0)\big].
--   $$
--
--   This moves the Lemma 3 bound from the warehouse echelon level $IL_0(t+L_0)=IP_0(t)-D_0$ back to the warehouse inventory position, where the warehouse's own $(r_0,Q_0)$ cost can be averaged.
--
--   **Formalization Note** The first line of App. A (9) is the definition of $\Gamma_0$. Expectations over $D_0$ are Bochner integrals against the Poisson law on $\mathbb N$, evaluated at the real argument $y-n$.
-- source:
--   Zhu, Chen, Hu & Yang, A simple heuristic policy for stochastic distribution inventory systems with fixed shipment costs, SSRN 2921743 (2020-09-08 copy), p. A4 (PDF 23), Online Appendix A, proof of Theorem 1, App. A (9)

import Mathlib
import Definitions.Def_DistribRQ_UpperBound_Model

open MeasureTheory ProbabilityTheory

namespace DistribRQ.UpperBound

/-- App. A (9), p. A4 (Zhu, Chen, Hu & Yang, SSRN 2921743): `Γ₀(y) ≤ Λ₀(y) + Σᵢ Cᵢ(rᵢ,Qᵢ)` for
every warehouse inventory position `y`. -/
theorem app_A_9 {N : ℕ} [NeZero N] (P : Primitives N) (π : Policy N) (κ : Kernel ℝ (Fin N → ℝ)) [IsMarkovKernel κ] (hκ : ∀ x, κ x (Feasible π x)ᶜ = 0) (c : Fin N → ℝ → ℝ) (hc : AdmissibleCharge P π c) (hc_meas : ∀ i, Measurable (c i)) (hc_nonneg : ∀ i z, 0 ≤ c i z) (y : ℝ) : Gamma0 P κ c y ≤ Lambda0 P π y + ∑ i, Ccost P π i := by sorry

end DistribRQ.UpperBound
