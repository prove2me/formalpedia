-- Prove2me | Theorems.Thm_ApproxDegComp_lemma_9
-- name    : ApproxDegComp.lemma_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:32:01.162592+00:00
-- url     : https://prove2.me/theorems/46394133-8bb1-4105-8fd0-45f1293d1271
-- title:
--   Lemma 9 — squarefree extraction of $R(\theta)=\mathbb E_{X^{(i)}\sim\rho_{\theta_i}}Q$ evaluates $Q$ under $\nu_{(1+z_i)/2}$
-- statement:
--   Let $Q:\{0,1\}^{mn}\to\mathbb R$, let $\{\rho_\theta:\theta\in\mathbb R\}$ be a differentiable family of probability measures on $\{0,1\}^m$, let $\kappa\ne0$, and let $\nu_0,\nu_1$ be probability measures on $\{0,1\}^m$ with
--
--   $$\nu_{(1+z)/2}=\rho_0+\frac z\kappa\rho_0'\qquad(z\in\{-1,1\}).$$
--
--   Split inputs into $n$ disjoint blocks of $m$ bits and let
--
--   $$R(\theta_1,\dots,\theta_n)=\mathbb E_{X^{(i)}\sim\rho_{\theta_i}}\bigl[Q(X^{(1)},\dots,X^{(n)})\bigr],$$
--
--   the blocks being drawn independently. If $R$ is analytic in a neighbourhood of $0$, then for every $z\in\{-1,1\}^n$
--
--   $$\mathcal S(R)\Bigl(\frac z\kappa\Bigr)=\mathbb E_{X^{(i)}\sim\nu_{(1+z_i)/2}}\bigl[Q(X^{(1)},\dots,X^{(n)})\bigr].$$
--
--   This turns the analytic object $R$ back into the Boolean world: evaluating its squarefree part at $z/\kappa$ gives the expectation of $Q$ when block $i$ is drawn from the measure attached to the bit $(1+z_i)/2$.
--
--   **Formalization Note** "Differentiable family" means each $\theta\mapsto\rho_\theta(x)$ is differentiable on $\mathbb R$; analyticity near $0$ is analyticity at $0$.
--
--   Differences from the source:
--   - encoding: Q : {0,1}^{mn} → ℝ a polynomial → Q any real function on the cube; reason: every real function on {0,1}^{mn} is a polynomial there; the same class
-- source:
--   Pednekar–Podder, On the Composition Theorem for Approximate Degree, Randomized and Exact Quantum Query Complexity, STOC 2027 submission (manuscript sha256 b9a66c7fdb2afdb57851f3734661cd2140455987b17e2a1e2400586be814092b), Lemma 9, p.16 (proof Appendix A, pp.43–45)

import Mathlib
import Definitions.Def_ApproxDegComp_sqfreeFun
import Definitions.Def_MemoryRegret_IsProbVec
import Definitions.Def_ApproxDegComp_zOf
import Definitions.Def_ApproxDegComp_blockExpect

namespace ApproxDegComp

/-- **Lemma 9**, p.16 (proof in Appendix A, pp.43–45).
Pednekar–Podder, *On the Composition Theorem for Approximate Degree, Randomized and Exact
Quantum Query Complexity*, STOC 2027 submission (manuscript sha256 b9a66c7f…), Lemma 9, p.16: "Let Q : {0, 1}^{mn} → ℝ be a polynomial. Let {ρ_θ : θ ∈ ℝ} be a
differentiable family of probability measures on {0, 1}^m and let ν₀ and ν₁ be probability
measures on {0, 1}^m such that, ν_{(1+z)/2} = ρ₀ + (z/κ)ρ′₀ for z ∈ {−1, 1} and some scalar κ ≠ 0.
Let X⁽¹⁾, …, X⁽ⁿ⁾ be n disjoint blocks of m bits each and X⁽ⁱ⁾'s are sampled independently from
ρ_{θᵢ}. Let R be defined as R(θ₁, …, θₙ) = E_{X⁽ⁱ⁾∼ρ_{θᵢ}}[Q(X⁽¹⁾, …, X⁽ⁿ⁾)]. If R is analytic in
a neighborhood of 0, then, S(R)(z/κ) = E_{X⁽ⁱ⁾∼ν_{(1+zᵢ)/2}}[Q(X⁽¹⁾, …, X⁽ⁿ⁾)], for every
z ∈ {−1, 1}ⁿ."

**Formalization Note** `Q` is any real function on the cube `{0,1}^{mn}` (every such function
is a polynomial there); coordinate `(i, j)` is bit `j` of block `i`. The expectation over
independent blocks is `blockExpect`. "Analytic in a neighbourhood of 0" is `AnalyticAt ℝ R 0`
(analyticity at a point is analyticity on a neighbourhood). `z ∈ {−1,1}ⁿ` is `zOf ∘ z`. -/
theorem lemma_9 (n m : ℕ) (Q : (Fin n × Fin m → Bool) → ℝ) (ρ : ℝ → (Fin m → Bool) → ℝ)
    (hρ : ∀ θ, MemoryRegret.IsProbVec (ρ θ)) (hρd : ∀ x, Differentiable ℝ (fun θ => ρ θ x))
    (ν : Bool → (Fin m → Bool) → ℝ) (hν : ∀ b, MemoryRegret.IsProbVec (ν b)) (κ : ℝ) (hκ : κ ≠ 0)
    (hrel : ∀ b x, ν b x = ρ 0 x + zOf b / κ * deriv (fun θ => ρ θ x) 0)
    (R : (Fin n → ℝ) → ℝ) (hR : ∀ θ, R θ = blockExpect (fun i => ρ (θ i)) Q)
    (han : AnalyticAt ℝ R 0) :
    ∀ z : Fin n → Bool,
      sqfreeFun R (fun i => zOf (z i) / κ) = blockExpect (fun i => ν (z i)) Q := by sorry

end ApproxDegComp
