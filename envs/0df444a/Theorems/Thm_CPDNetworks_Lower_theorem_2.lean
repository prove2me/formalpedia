-- Prove2me | Theorems.Thm_CPDNetworks_Lower_theorem_2
-- name    : CPDNetworks.Lower.theorem_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T06:27:04.62535+00:00
-- url     : https://prove2.me/theorems/649c1a4d-cc90-4d27-933e-5a8f118adfa2
-- title:
--   Theorem 2 — changes of energy R with ½μ_n²n(n−1)/(1−2μ_n(n−1)) ≤ C_η are undetectable at a known time: every level-α test has type II error ≥ β
-- statement:
--   Consider $T$ independent snapshots of an inhomogeneous random graph on $n\ge2$ vertices with missing links, and the problem (P1) of testing for a change of the connection matrix at a given time $\tau$, $1\le\tau\le T-1$. Let $\alpha\in(0,1)$ and $\beta\in(0,1-\alpha]$ be given significance levels, $\eta=\alpha+\beta$, and
--   $$C_\eta=\log\big(1+4(1-\eta)^2\big),\qquad \varepsilon_n=(2C_\eta)^{1/4}\omega_n^{-1/2},\qquad \tilde\rho_n=(1-\varepsilon_n)\frac{\omega_n}{n-1}.$$
--   Assume $\omega_n>\sqrt{2C_\eta}$, $\omega_n\ge4\sqrt{2C_\eta}$ and $\omega_n\le(n-1)/2$. Let $R>0$ and
--   $$\mu_n=\frac{TR^2}{\omega_n}\cdot\frac1{(1-\tilde\rho_n)(n-1)(1-\varepsilon_n)},$$
--   and suppose that
--   $$\mu_n(n-1)<\frac12\qquad\text{and}\qquad \frac{\frac12\mu_n^2\,n(n-1)}{1-2\mu_n(n-1)}\le C_\eta .$$
--   Then every test $\psi$ of level $\alpha$, i.e. with $\sup_{(\Theta^0,\Pi)\in\mathcal S_n(\omega_n)}\mathrm P_{(\Theta^0,\Pi)}\{\psi=1\}\le\alpha$, has type II error
--   $$\beta(\psi,R)=\sup_{\{(\Theta^0+\Delta\Theta^\tau,\Pi),(\Theta^0,\Pi)\}\in\mathcal W^\tau_{n,T}(\omega_n,R)}\mathrm P_{(\Theta^0+\Delta\Theta^\tau,\Pi),(\Theta^0,\Pi)}\{\psi=0\}\ \ge\ \beta .$$
--   In words: changes of energy $R$ in this range cannot be detected by any $\alpha$-level test with type II error smaller than $\beta$. Since $\mu_n(n-1)$ is of order $TR^2/\omega_n$, for $\eta<1$ the condition holds for all $R\le c_\eta(\omega_n/T)^{1/2}$ with $c_\eta>0$ depending only on $\eta$, which is the order $(\omega_n/T)^{1/2}$ lower bound on the minimax detection boundary $\mathcal R^*_{n,\tau}$ that Theorem 2 asserts.
--
--   This is the lower half of the paper's minimax result for a known change point: together with the matching upper bound of Theorem 1 it identifies $(\omega_n/T)^{1/2}$ as the detection rate.
--
--   **Formalization Note** The page states $\mathcal R^*_{n,\tau}\ge(2C_\eta)^{1/4}(\omega_n/T)^{1/2}$ under $\omega_n>\sqrt{2C_\eta}$, and its proof ends with the condition (29), $TR^2/\omega_n\le\sqrt{2C_\eta}(1-\tilde\rho_n)(1-\varepsilon_n)(1-1/n)(1+2\sqrt{2C_\eta}/n)^{-1}$. That route rests on a Rademacher-chaos bound (Step 4 and the first display of p. 37) printed without the factor $\|\mathbf 1_n\mathbf 1_n^{\mathsf T}-\mathrm{id}_n\|_{2\to2}=n-1$; as printed those displays are false for large $n$, and condition (29) allows $\mu_n(n-1)$ close to $\sqrt{2C_\eta}$, which exceeds $1$ for small $\eta$, where the second moment of the likelihood ratio is exponentially large. What is stated here is the conclusion of the same proof (Steps 1–3, display (25)) with the corrected Step 4 bound $\exp\{\frac12\mu_n^2n(n-1)/(1-2\mu_n(n-1))\}$, required to be at most $1+4(1-\eta)^2=e^{C_\eta}$; this is the paper's "lower bound condition" (p. 9) in the form "no level-$\alpha$ test has type II error smaller than $\beta$" (p. 37). Two hypotheses are added and disclosed: $\omega_n\ge4\sqrt{2C_\eta}$ ($\varepsilon_n\le1/2$) and $\omega_n\le(n-1)/2$ ($\tilde\rho_n\le1/2$), which make the paper's priors valid. Tests are arbitrary Boolean functions of the observation; the level condition is the supremum over the whole null class, every sampling matrix $\Pi$ included. When $\eta=1$, $C_\eta=0$ and the hypotheses cannot hold for $R>0$, as in the paper, where $\beta=1-\alpha$ is the trivial boundary.
-- source:
--   Enikeeva and Klopp, Change-point detection in dynamic networks with missing links, arXiv:2106.14470v2, p. 10, Theorem 2; proof pp. 33–37 (App. B.1–B.3, displays (25)–(29))

import Mathlib
import Definitions.Def_HighDimProb_RandomMatrices_matrixOpNorm
import Definitions.Def_CPDNetworks_Lower_Setting

namespace CPDNetworks.Lower

/-- **Theorem 2** (Enikeeva–Klopp, p. 10), in the form its proof establishes (pp. 33–37), with the
Rademacher-chaos step corrected. Let `α ∈ (0, 1)`, `β ∈ (0, 1 − α]`, `η = α + β`,
`C_η = log(1 + 4(1 − η)²)`, `n ≥ 2`, `1 ≤ τ ≤ T − 1`, `ω_n > √(2C_η)`, and additionally
`ω_n ≥ 4√(2C_η)` and `ω_n ≤ (n − 1)/2`. If `R > 0` and
`μ_n = (TR²/ω_n)/((1 − ρ̃_n)(n − 1)(1 − ε_n))` satisfies `μ_n(n − 1) < 1/2` and
`½μ_n²n(n − 1)/(1 − 2μ_n(n − 1)) ≤ C_η`, then every test of level `α` in problem (P1) has type II
error at least `β` against `𝒲^τ_{n,T}(ω_n, R)`: changes of energy `R` are not detectable. -/
theorem theorem_2 (n T τ : ℕ) (ω α β R : ℝ) (hn : 2 ≤ n) (hτ : 1 ≤ τ) (hτT : τ < T)
    (hα : 0 < α) (hα1 : α < 1) (hβ : 0 < β) (hβα : β ≤ 1 - α)
    (hω : Real.sqrt (2 * Ceta α β) < ω) (hε : 4 * Real.sqrt (2 * Ceta α β) ≤ ω)
    (hωn : ω ≤ ((n : ℝ) - 1) / 2) (hR : 0 < R)
    (hμ : 2 * muN n T ω α β R * ((n : ℝ) - 1) < 1)
    (h28 : muN n T ω α β R ^ 2 * n * ((n : ℝ) - 1) ≤
      2 * Ceta α β * (1 - 2 * muN n T ω α β R * ((n : ℝ) - 1)))
    (ψ : Obs n T → Bool) (hψ : typeI (T := T) ω ψ ≤ α) :
    β ≤ typeII {τ} ω R ψ := by sorry

end CPDNetworks.Lower
