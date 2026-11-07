-- Prove2me | Theorems.Thm_BlockLewisIPM_lemma_34
-- name    : BlockLewisIPM.lemma_34
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:53:23.272257+00:00
-- url     : https://prove2.me/theorems/bf9973d0-d5d6-4e37-99f4-24f2a9d5e8e8
-- title:
--   Lemma 34 — one-step change of the potential
-- statement:
--   Consider one call of Algorithm 1 at an $\epsilon$-centered triplet $(x,s,\rho)$, with an $\alpha$-approximation $(\bar x,\bar\tau)$ of $(x,\tau)$, $\tau=\tau(x)$, and a valid sampling $R$. Let $\bar\mu$ be a $10\alpha$-approximation of $\mu$ and $\|\Gamma\|_\infty\le\epsilon^2$. Then
--
--   $$\mathbb E[\Psi(\mu^{(\mathrm{new})},x^{(\mathrm{new})})]\le\Psi(\mu,x)+\langle\nabla^{\mathrm{loc}}_\mu\Psi(\mu,x),g\rangle+\Bigl(1-\frac\theta3\Bigr)\beta\|\nabla^{\mathrm{loc}}_\mu\Psi(\mu,x)\|^*_{2,\tau+\infty}+O(\beta^2+\lambda\beta^2\epsilon^2)\|\nabla_\Gamma\Psi(\mu,x)\|^*_{\tau+\infty}.$$
--
--   This is the potential analysis in Bregman form, without differentiating the inverse Hessian metric. Here $K_0$ is the constant of $\lesssim$ and $O(\cdot)$, which depends only on a bound $N$ on the block sizes. The constant $C$ is sufficiently large, and $C_{\mathrm{Var}}$ is then sufficiently large. Expectations are taken conditionally on the event of items 4 and 5 of Definition 19.
--
--   Differences from the source:
--   - reading: (x̄, τ̄) an α-approximation (the lemma as printed) → also (x, s, ρ) ϵ-centered with the ϵ of Algorithm 1 and all lines of Algorithm 1 hold; reason: §4.2, p.22: "We will suppose (x, s, ρ) is ϵ-central for the rest of the section"
--   - reading: constants hidden in ≲ and O(·), C "sufficiently large" (p.10), C_Var "sufficiently large" (Definition 19) → ∃ K₀ C₀ for each bound N on block sizes, ∀ C ≥ C₀, ∃ a C_Var threshold depending on C only, besides C_Var ≥ C_norm; reason: §3.1 puts C above the hidden constants, Algorithm 1 fixes β without n_i, n_i β ≲ 1 (p.24) needs N, and Definition 19 asks C_Var ≥ C_norm and "a sufficiently large constant"
--   - reading: E[·] → the expectation conditional on the event of Definition 19 items 4 and 5, with integrability stated; reason: x^(new) ∈ int K, and so Ψ, Γ and τ at x^(new), are only known on that event; outside it the terms have junk values
--   - reading: A any matrix → A of full column rank; reason: P(·) and (A⊤T⁻¹∇²Φ⁻¹A)⁻¹ are defined on p.10 for full column rank
--   - encoding: m unrestricted → m ≥ 2; reason: θ = 1/(10 log m) is undefined at m = 1; this only excludes an undefined case
-- source:
--   Zhang, Wright, A Fast Lewis-weight Interior Point Method for Linear Optimization over Product-Domain (manuscript, sha256 66072000…), Lemma 34, p.30

import Mathlib
import Definitions.Def_BlockLewisIPM_ShortStep

open Matrix MeasureTheory ProbabilityTheory

namespace BlockLewisIPM

open Instance

/-- **Lemma 34** (potential change), p.30. Zhang, Wright, *A Fast Lewis-weight Interior Point Method for
Linear Optimization over Product-Domain* (manuscript, sha256 66072000…).

**Formalization Note.** Conventions of `lemma_28`. `‖Γ‖_∞ ≤ ϵ²` is part of `ϵ`-centering in `IsStepCall`.
The page's list mentions a `γ` that does not occur in the display. `∇_ΓΨ = (ψ′(Γ_i))_i`. -/
theorem lemma_34 (N : ℕ) : ∃ K₀ C₀ : ℝ, 0 < K₀ ∧ 10000 ≤ C₀ ∧ ∀ C ≥ C₀, ∃ Cv₀ : ℝ,
    ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (I : Instance ι), I.Standing N →
    ∀ Cvar ≥ Cv₀,
    ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (R : Ω → ι → ℝ)
      (D : I.StepData), IsStepCall (I.par C) Cvar D μ R →
    let P := I.par C
    let ν := stepLaw P Cvar D μ R
    let τ := I.tau P D.x
    let μ₀ := I.mu P D.x D.s D.ρ
    let loc := I.gradLoc P.lam μ₀ D.x
    Integrable (fun ω => I.Psi P.lam (D.muNew P (R ω)) (D.xNew (R ω))) ν ∧
    ∫ ω, I.Psi P.lam (D.muNew P (R ω)) (D.xNew (R ω)) ∂ν ≤
      I.Psi P.lam μ₀ D.x + loc ⬝ᵥ D.g + (1 - P.θ / 3) * P.β * dualMixedBlockNorm P.Cnorm τ loc +
        K₀ * (P.β ^ 2 + P.lam * P.β ^ 2 * P.ϵ ^ 2) *
          dualMixedNorm P.Cnorm τ (I.gradGamPsi P.lam μ₀ D.x) := by sorry

end BlockLewisIPM
