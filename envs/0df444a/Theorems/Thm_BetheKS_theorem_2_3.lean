-- Prove2me | Theorems.Thm_BetheKS_theorem_2_3
-- name    : BetheKS.theorem_2_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:38:09.636232+00:00
-- url     : https://prove2.me/theorems/6ce9cde0-3cb2-4a26-9c14-aeb523eb9f46
-- title:
--   Theorem 2.3 (Weak recovery) — rounding the informative Bethe-Hessian embedding gives $\mathrm{ov}\ge\frac{\pi_{\min}}{64r^2(r-1)}\sum c_{\mu_i}^2$
-- statement:
--   Assume the SBM parameters are fixed and satisfy (2.1). Let $c_\mu>0$ be the constants of Theorem 2.2, and set $\pi_{\min}:=\min_a\pi_a$. For every fixed choice of the parameters there is a randomized polynomial-time algorithm, with constants depending on those parameters, that rounds the informative Bethe-Hessian embedding to an output $\widehat\sigma_n$ satisfying, with probability $1-o_n(1)$,
--   $$
--   \operatorname{ov}(\sigma,\widehat\sigma_n)\ \ge\ \frac{\pi_{\min}}{64r^2(r-1)}\sum_{i\ge2,\ |\mu_i|>\sqrt d}c_{\mu_i}^2 .
--   $$
--   In particular, weak recovery is possible whenever $\max_{i\ge2}|\mu_i|>\sqrt d$.
--
--   Formally: (a) constants with the projection property of Theorem 2.2 exist; (b) for every such family $c$, the randomized rounding of App. F built from $c$ (orthonormal basis of $E_n\cap\mathbf 1^\perp$, truncation at $M=4\sqrt2(r-1)/\sqrt{\pi_{\min}S}$, independent labels with $\mathbb P(\widehat\sigma_n(u)=b\mid G_n)=(1+(Rf_u)_b)/r$) achieves the bound with probability tending to one, for every choice the algorithm leaves open; (c) if $\max_{i\ge2}|\mu_i|>\sqrt d$, then for every such $c$ there is $\varepsilon>0$ with $\operatorname{ov}(\sigma,\widehat\sigma_n)\ge\varepsilon$ with probability tending to one.
--
--   This is weak recovery by a spectral method on $n\times n$ Hermitian matrices down to the Kesten–Stigum threshold, for every fixed $d>1$.
--
--   Differences from the source:
--
--   - reading: 'there is a randomized polynomial-time algorithm' → the explicit algorithm of App. F, for every choice of eigenbases of H(±√d, G), of the basis U_n, of R and of a fallback law used when dim(E_n ∩ 1^⊥) ≠ m; no machine model; reason: the paper analyses exactly this algorithm; its inputs are real, and exact eigenvectors are not bit-computable
--   - reading: 'Let c_μ > 0 be the constants in Theorem 2.2' → (a) such constants exist, and (b) the bound holds for every family c with the projection property; reason: App. F uses only the projection property; the universal reading is the stronger one
--   - reading: 'weak recovery is possible whenever max_{i≥2}|μ_i| > √d' → for every valid c there is ε > 0 with P(ov ≥ ε) → 1 for the same algorithm, uniformly over its choices; reason: weak recovery means overlap bounded below by a positive constant w.p. → 1 (p.5)
--   - encoding: Σ over i ≥ 2 with |μ_i| > √d, d = μ_1 ≥ |μ_2| ≥ … → the multiset of informative eigenvalues with one copy of d removed; reason: the same multiset, written basis-free
--   - encoding: eigenvalues of Q counted with multiplicity → real roots of the characteristic polynomial of Q, with multiplicity; reason: Q is diagonalizable with real spectrum, so algebraic and geometric multiplicities agree
--   - encoding: n → ∞ with |σ⁻¹(i)| = π_i n → n → ∞ along 𝒩_π = {n : π_i n ∈ ℕ ∀ i}, for every sequence of exact-size label maps σ_n; reason: the paper's deterministic community-size convention (p.4); the statement is uniform over the labelings
--   - encoding: π a distribution on [r] → every π_a > 0; reason: the r eigenfunctions orthonormal in L²(π) that the paper uses exist only then; excludes undefined cases
--   - encoding: edge probability P_{σ(u)σ(v)}/n → min(1, P_{σ(u)σ(v)}/n); reason: affects only finitely many n, not the limits
--   - encoding: S = 0, where L = 0 and M = 4√2(r−1)/L is undefined (App. F: "If S = 0 we are done") → the algorithm is still built, with Lean's x/0 = 0 giving M = 0 and f_u = x_u/‖x_u‖, a valid law; reason: the bound is then 0 and the centered overlap is always nonnegative; no instance of the claim changes
-- source:
--   Dong, McKenzie, Bethe Hessian Recovery through the Kesten–Stigum Regime, arXiv:2610.41802 (held version, sha256 4da41e16…), Theorem 2.3, p.5 (PDF p.6); proof in App. F, pp.26–27

import Mathlib
import Definitions.Def_BetheKS_HasProjProperty
import Definitions.Def_BetheKS_roundingAlg

set_option autoImplicit false

namespace BetheKS

/-- **Theorem 2.3 (Weak recovery)** — Dong, McKenzie, *Bethe Hessian Recovery through the
Kesten–Stigum Regime*, arXiv:2610.41802 (held version, sha256 4da41e16…), p.5 (PDF p.6); proof in
App. F, pp.26–27.

For fixed SBM parameters satisfying (2.1):
1. constants `c_µ > 0` with the projection property of Theorem 2.2 exist;
2. for **every** such family `c`, the randomized rounding of App. F built from `c` outputs `σ̂ₙ` with
   `ov(σ, σ̂ₙ) ≥ π_min/(64 r²(r−1)) · ∑_{i≥2, |µᵢ|>√d} c²_{µᵢ}` with probability `1 − oₙ(1)`, for every
   choice the algorithm leaves open;
3. if `max_{i≥2} |µᵢ| > √d` (i.e. `m ≥ 1`), then for every such `c` there is `ε > 0` with
   `ov(σ, σ̂ₙ) ≥ ε` with probability `1 − oₙ(1)` (weak recovery).

**Formalization Note.** "There is a randomized polynomial-time algorithm" is formalized by the
explicit algorithm the paper analyses (App. F), quantified over all of its choices
(`RoundingSucceeds`); no machine model is imposed. `n → ∞` runs over `𝒩_π`, uniformly over exact-size
labelings. The sum over `i ≥ 2` is the multiset of informative eigenvalues with one copy of
`µ₁ = d` removed. -/
theorem theorem_2_3 {r : ℕ} (p : SBMParams r) :
    (∃ c : ℝ → ℝ, HasProjProperty p c) ∧
    (∀ c : ℝ → ℝ, HasProjProperty p c →
      RoundingSucceeds p c (piMin p / (64 * (r : ℝ) ^ 2 * ((r : ℝ) - 1)) * sumS p c)) ∧
    (0 < mDim p → ∀ c : ℝ → ℝ, HasProjProperty p c → ∃ ε : ℝ, 0 < ε ∧ RoundingSucceeds p c ε) := by sorry

end BetheKS
