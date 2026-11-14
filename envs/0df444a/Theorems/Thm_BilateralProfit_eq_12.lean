-- Prove2me | Theorems.Thm_BilateralProfit_eq_12
-- name    : BilateralProfit.eq_12
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T02:20:19.829198+00:00
-- url     : https://prove2.me/theorems/c8f18b1e-cafe-468d-a30a-d706431811ef
-- title:
--   Eq. (12) — the information $\mathcal I_\rho(a)$ as averaged Bernoulli KL divergences, and Pinsker
-- statement:
--   Let $\rho$ be a distribution on $G_K\times\mathcal A$ and $a\in\mathcal A$. Under $\rho$ the feedback $z_a(V)$ is a Bernoulli variable with success probability $P_0(a)$, or $P_{a'}(a)$ conditionally on $A=a'$, and
--   $$\begin{aligned}\mathcal I_\rho(a)&=\sum_{a'\in\mathcal A}\mathbb P_\rho(A=a')\Big[\sum_{z\in\{0,1\}}\mathbb P_\rho(z_a(V)=z\mid A=a')\log\frac{\mathbb P_\rho(z_a(V)=z\mid A=a')}{\mathbb P_\rho(z_a(V)=z)}\Big]\\&=\sum_{a'\in\mathcal A}\mathbb P_\rho(A=a')\,D_{\mathrm{KL}}\big(\mathrm{Bern}(P_{a'}(a))\,\|\,\mathrm{Bern}(P_0(a))\big)\\&\ge2\sum_{a'\in\mathcal A}\mathbb P_\rho(A=a')\big(P_{a'}(a)-P_0(a)\big)^2 .\end{aligned}$$
--
--   The last inequality is Pinsker's inequality for Bernoulli laws; combined with the contradiction hypothesis it gives Claim 4.4 in the proof of Theorem 4.2.
--
--   **Formalization Note** $D_{\mathrm{KL}}(\mathrm{Bern}(p)\|\mathrm{Bern}(q))$ is the published `klBern p q`. Conditional probabilities given $A=a'$ are set to $0$ when $\mathbb P_\rho(A=a')=0$; such terms carry the factor $\mathbb P_\rho(A=a')=0$.
--
--   Differences from the source:
--   - encoding: the grid $G_K$ of step size $1/K$ → hypothesis $0<K$; reason: the step size $1/K$ presupposes $K\ge1$ (Lemma A.6: "for every integer $K\ge1$")
--   - encoding: $D_{\mathrm{KL}}(\mathrm{Bern}(P_{a'}(a))\|\mathrm{Bern}(P_0(a)))$ and conditional probabilities → `klBern` and ratios with $x/0=0$; reason: terms with $\mathbb P_\rho(A=a')=0$ are multiplied by $0$; otherwise $P_{a'}(a)=0$ when $P_0(a)=0$ and $P_{a'}(a)=1$ when $P_0(a)=1$, where `klBern` takes the true value $0$
-- source:
--   Brüstle, di Gregorio, Fusco, Leonardi, Regret Bounds for Profit Maximization in Bilateral Trade: Learning the Best Posted-Price Mechanism (manuscript, STOC 2027 submission, sha256 e91e81279505b765c7c96c219d674c0fbbbd6ca47a00da8fe228d498ca25ac87), eq. (12), pp.19–20 (PDF 21–22), in the proof of Theorem 4.2

import Mathlib
import Definitions.Def_RegretBandits_Stochastic_klBernoulli
import Definitions.Def_BilateralProfit_Analysis

namespace BilateralProfit

open RegretBandits.Stochastic (klBern)

/-- **Equation (12)**, Brüstle, di Gregorio, Fusco, Leonardi (manuscript, sha256 e91e8127…),
pp.19–20 (PDF 21–22), in the proof of Theorem 4.2: for every distribution `ρ` on `G_K × 𝒜` and
every action `a`,
`ℐ_ρ(a) = Σ_{a′} P_ρ(A = a′) [Σ_z P_ρ(z_a(V) = z | A = a′) log (P_ρ(z_a(V) = z | A = a′)/P_ρ(z_a(V) = z))]
       = Σ_{a′} P_ρ(A = a′) D_KL(Bern(P_{a′}(a)) ‖ Bern(P0(a)))
       ≥ 2 Σ_{a′} P_ρ(A = a′) (P_{a′}(a) − P0(a))²`.

**Formalization Note.** `D_KL(Bern(p) ‖ Bern(q))` is the published `klBern p q`. The conditional
probabilities use `x / 0 = 0` when `P_ρ(A = a′) = 0`; those terms are multiplied by
`P_ρ(A = a′) = 0`. In the remaining terms `P_{a′}(a) = 0` whenever `P0(a) = 0` and `P_{a′}(a) = 1`
whenever `P0(a) = 1`, where `klBern` takes its correct value `0`. -/
theorem eq_12 (K : ℕ) (hK : 0 < K) (ρ : Grid K × Act K → ℝ) (hρ : IsDist ρ) (a : Act K) :
    info ρ a = ∑ a', margA ρ a' * ∑ z : Bool,
        (jointP ρ a a' z / margA ρ a') *
          Real.log ((jointP ρ a a' z / margA ρ a') / zP ρ a z) ∧
      ∑ a', margA ρ a' * ∑ z : Bool,
        (jointP ρ a a' z / margA ρ a') *
          Real.log ((jointP ρ a a' z / margA ρ a') / zP ρ a z) =
        ∑ a', margA ρ a' * klBern (Pcond ρ a' (pt K a.1)) (P0 ρ (pt K a.1)) ∧
      2 * ∑ a', margA ρ a' * (Pcond ρ a' (pt K a.1) - P0 ρ (pt K a.1)) ^ 2 ≤
        ∑ a', margA ρ a' * klBern (Pcond ρ a' (pt K a.1)) (P0 ρ (pt K a.1)) := by sorry

end BilateralProfit
