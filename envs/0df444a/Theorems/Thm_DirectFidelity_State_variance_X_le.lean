-- Prove2me | Theorems.Thm_DirectFidelity_State_variance_X_le
-- name    : DirectFidelity.State.variance_X_le
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T02:29:41.978657+00:00
-- url     : https://prove2.me/theorems/b2636ae8-c09b-4d26-8f88-eb0db100f618
-- title:
--   (12)–(14), p. 6 — $\mathrm{Var}(X) \le \mathrm{tr}(\sigma^2) - [\mathrm{tr}(\rho\sigma)]^2 \le 1$
-- statement:
--   Let $\rho$ be a pure state and $\sigma$ a state on $n$ qubits, and let $X = \chi_\sigma(k)/\chi_\rho(k)$ with $k$ drawn from $\Pr(k) = \chi_\rho(k)^2$. Then
--   $$\mathrm{Var}(X) = \mathbb E(X^2) - (\mathbb E X)^2 \;\le\; \mathrm{tr}(\sigma^2) - [\mathrm{tr}(\rho\sigma)]^2 \;\le\; 1 ,$$
--   where $(\mathbb E X)^2$ is written as $[\mathrm{tr}(\rho\sigma)]^2$.
--
--   The variance bound is what lets Chebyshev's inequality give (5) with $\ell = \lceil 1/(\varepsilon^2\delta)\rceil$ samples, independently of the dimension.
--
--   **Formalization Note.** The paper prints (13) as an equality, $\mathrm{Var}(X_i) = \sum_k[\chi_\sigma(k)]^2 - [\mathrm{tr}(\rho\sigma)]^2$. That is false in general: $\mathbb E(X^2)$ only sums $\chi_\sigma(k)^2$ over the labels with $\chi_\rho(k)\neq0$ (for $n = 1$, $\rho = |0\rangle\langle0|$, $\sigma = |+\rangle\langle+|$ one has $\mathrm{Var}(X) = 1/4$ while (13) gives $3/4$). The statement therefore has "$\le$" in place of (13)'s "$=$"; the conclusion of (14), $\mathrm{Var}(X)\le 1$, is unchanged and is all that (5) uses. $\mathbb E(X^2)$ is the finite sum $\sum_k \Pr(k)X(k)^2$; the junk value at $\chi_\rho(k) = 0$ carries weight $0$.
-- source:
--   Flammia and Liu, Direct fidelity estimation from few Pauli measurements, arXiv:1104.4695v3, p. 6, §Bounding the Failure Probabilities, (12)–(14) ((13) corrected to an inequality)

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_DirectFidelity_State_Setting

namespace DirectFidelity.State

theorem variance_X_le (n : ℕ) (ρ σ : Matrix (Q n) (Q n) ℂ) (hρ : IsPure ρ)
    (hσ : WildeQIT.IsDensityOperator σ) :
    ∑ k : P n, prob ρ k * X ρ σ k ^ 2 - ((ρ * σ).trace).re ^ 2 ≤
        ((σ * σ).trace).re - ((ρ * σ).trace).re ^ 2 ∧
      ((σ * σ).trace).re - ((ρ * σ).trace).re ^ 2 ≤ 1 := by sorry

end DirectFidelity.State
