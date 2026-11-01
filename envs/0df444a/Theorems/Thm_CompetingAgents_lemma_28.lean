-- Prove2me | Theorems.Thm_CompetingAgents_lemma_28
-- name    : CompetingAgents.lemma_28
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:25:08.812459+00:00
-- url     : https://prove2.me/theorems/35e7c1a5-3da3-41ff-9b0b-2cd559dd6977
-- title:
--   Lemma 28 — derivative formula (E.1) for $\omega_i$, and $s-\omega_i(s;\beta)$ is strictly increasing
-- statement:
--   Let $\varphi_\sigma$ be the $N(0,\sigma^2)$ density. Suppose Assumption 1, $\sigma^2>1/(\alpha_i\sqrt{2\pi e})$, and $\beta\in\mathcal B$. Then for every $s$ with $x_i^*(\beta,s)\in\mathrm{Int}(\mathcal X)$,
--
--   $$\nabla_s\omega_i(s;\beta)=\frac{\varphi_\sigma'(s-\omega_i(s;\beta))\,\beta^TH^{-1}\beta}{1+\varphi_\sigma'(s-\omega_i(s;\beta))\,\beta^TH^{-1}\beta},\qquad H=\nabla^2c_i\big(x_i^*(\beta,s)-Z_i\big),\tag{E.1}$$
--
--   and, if $x_i^*(\beta,s)\in\mathrm{Int}(\mathcal X)$ for all $s$, then $h_i(s;\beta)=s-\omega_i(s;\beta)$ is strictly increasing in $s$.
--
--   The formula drives every contraction bound of the paper: $|\varphi_\sigma'|\le1/(\sigma^2\sqrt{2\pi e})$ and $\beta^TH^{-1}\beta\le1/\alpha_i$.
--
--   **Formalization Note** The derivative formula needs the interior hypothesis only at the threshold $s$ where it is evaluated, as printed. For the monotonicity of $h_i$, a claim about all $s$, the interior hypothesis is assumed at every threshold $s$, for the given $\beta\in\mathcal B$. $H$ is the derivative of the gradient of $c_i$, a linear map $\mathbb R^d\to\mathbb R^d$, and $H^{-1}$ is its inverse; it is invertible because $H\succeq\alpha_iI$.
--
--   Differences from the source:
--
--   - generalization: $c_i\in\mathcal C\subset L^2(\tilde{\mathcal X},dx)$, $\mathcal C$ convex and compact (p.6) → any cost function satisfying Assumption 1; reason: the statement does not use $\mathcal C$; every cost function of the source satisfies Assumption 1
--   - encoding: $\mathbb E_\epsilon[U_i(x;\beta,s)]$, the expected utility over $\epsilon\sim N(0,\sigma^2 I_d)$ → formula (2.2), $-c_i(x-Z_i)+1-\Phi_\sigma(s-\beta^Tx)$, taken as the definition; reason: (2.2) is the paper's own evaluation of the expectation; the two agree for $\|\beta\|=1$ (proved in the verification file)
--   - encoding: $x_i^*(\beta,s)=\operatorname{argmax}_{x\in\mathcal X}\mathbb E_\epsilon[U_i(x;\beta,s)]$ → a chosen maximizer over $\mathcal X$ (the point $0$ if there were none); reason: under Assumption 1 a maximizer exists and under the noise condition it is unique (Proposition 1), so in every statement the choice is the argmax
--   - reading: $x_i^*(\beta,s)\in\mathrm{Int}(\mathcal X)$ → for (E.1), $x_i^*(\beta,s)\in\mathrm{Int}(\mathcal X)$ at the threshold $s$ where the derivative is taken; for the monotonicity of $h_i$, at every $s\in\mathbb R$, at the given $\beta$; reason: (E.1) is a pointwise claim; strict monotonicity of $h_i$ is a claim about all thresholds $s$
-- source:
--   Sahoo, Wager, Policy Learning with Competing Agents, arXiv:2204.01884v5, Lemma 28, (E.1), p.31

import Mathlib
import Definitions.Def_CompetingAgents_bestResponse

open scoped RealInnerProductSpace

namespace CompetingAgents

/-- Lemma 28 (Sahoo, Wager, *Policy Learning with Competing Agents*, arXiv:2204.01884v5, Lemma 28,
(E.1), p.31). Let `φ_σ` be the `N(0, σ²)` density. Under Assumption 1, if `σ² > 1/(αᵢ√(2πe))` and
`x*ᵢ(β, s) ∈ Int(𝒳)`, then
`∇ₛ ωᵢ(s; β) = φ'_σ(s − ωᵢ(s; β)) βᵀH⁻¹β / (1 + φ'_σ(s − ωᵢ(s; β)) βᵀH⁻¹β)` with
`H = ∇²cᵢ(x*ᵢ(β, s) − Zᵢ)`, and `hᵢ(s; β) = s − ωᵢ(s; β)` is strictly increasing in `s`.

**Formalization Note.** The derivative formula is claimed at every threshold `s` whose best
response is interior, as printed; the monotonicity of `hᵢ` is a claim about all `s`, and for it the
interior condition is assumed at every threshold `s`, for the given `β ∈ 𝔅`. The Hessian `H` is the derivative of the
gradient of `cᵢ`, a linear map `ℝ^d → ℝ^d`, and `H⁻¹` is its inverse
(`ContinuousLinearMap.inverse`, which is the true inverse here because `H ≥ αᵢ I` by strong
convexity). `φ'_σ` is `deriv` of the density. -/
theorem lemma_28 {d : ℕ} {ι : Type*} [Fintype ι] (M : Model d ι) (hA1 : Assumption1 M) (i : ι)
    (hσ : 1 / (M.α i * Real.sqrt (2 * Real.pi * Real.exp 1)) < M.σ ^ 2)
    (β : Cov d) (hβ : β ∈ Metric.sphere (0 : Cov d) 1) :
    (∀ s : ℝ, bestResponse M i β s ∈ interior M.X →
      let H := fderiv ℝ (gradient (M.c i)) (bestResponse M i β s - M.Z i)
      let b := ⟪β, H.inverse β⟫
      let φ' := deriv (noiseDensity M) (s - omega M i β s)
      HasDerivAt (fun s' => omega M i β s') (φ' * b / (1 + φ' * b)) s) ∧
    ((∀ s : ℝ, bestResponse M i β s ∈ interior M.X) →
      StrictMono (fun s => s - omega M i β s)) := by sorry

end CompetingAgents
