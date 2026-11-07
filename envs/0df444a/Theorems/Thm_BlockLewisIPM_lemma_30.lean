-- Prove2me | Theorems.Thm_BlockLewisIPM_lemma_30
-- name    : BlockLewisIPM.lemma_30
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:52:23.550025+00:00
-- url     : https://prove2.me/theorems/789e4fd1-4e0d-4cb7-897f-0a30b6ce4a79
-- title:
--   Lemma 30 — stability of the Lewis weights over one short step
-- statement:
--   Consider one call of Algorithm 1 at an $\epsilon$-centered triplet $(x,s,\rho)$, with an $\alpha$-approximation $(\bar x,\bar\tau)$ of $(x,\tau)$, $\tau=\tau(x)$, and a valid sampling $R$.
--
--   With $\tau^{(\mathrm{new})}=\tau(x^{(\mathrm{new})})$ and $\delta_\tau=\tau^{(\mathrm{new})}-\tau$,
--
--   1. $\|T^{-1}\delta_\tau\|_\infty\lesssim\beta$ with high probability;
--   2. $\|\mathbb E[(T^{-1}\delta_\tau)^2]\|_{\tau+\infty}\lesssim\beta^2$;
--   3. $\|T^{-1}\mathbb E[\delta_\tau]\|_{\tau+\infty}\le\sqrt{p/(2-p)}\,\beta+O((C_{\mathrm{norm}}^{-1}+\alpha+\beta)\beta)$.
--
--   The factor $\sqrt{p/(2-p)}<1$ is what later leaves room in the potential decrease. Here $K_0$ is the constant of $\lesssim$ and $O(\cdot)$, which depends only on a bound $N$ on the block sizes. The constant $C$ is sufficiently large, and $C_{\mathrm{Var}}$ is then sufficiently large. Expectations are taken conditionally on the event of items 4 and 5 of Definition 19.
--
--   Differences from the source:
--   - reading: (x̄, τ̄) an α-approximation (the lemma as printed) → also (x, s, ρ) ϵ-centered with the ϵ of Algorithm 1 and all lines of Algorithm 1 hold; reason: §4.2, p.22: "We will suppose (x, s, ρ) is ϵ-central for the rest of the section"
--   - reading: constants hidden in ≲ and O(·), C "sufficiently large" (p.10), C_Var "sufficiently large" (Definition 19) → ∃ K₀ C₀ for each bound N on block sizes, ∀ C ≥ C₀, ∃ a C_Var threshold depending on C only, besides C_Var ≥ C_norm; reason: §3.1 puts C above the hidden constants, Algorithm 1 fixes β without n_i, n_i β ≲ 1 (p.24) needs N, and Definition 19 asks C_Var ≥ C_norm and "a sufficiently large constant"
--   - reading: E[·] → the expectation conditional on the event of Definition 19 items 4 and 5, with integrability stated; reason: x^(new) ∈ int K, and so Ψ, Γ and τ at x^(new), are only known on that event; outside it the terms have junk values
--   - reading: A any matrix → A of full column rank; reason: P(·) and (A⊤T⁻¹∇²Φ⁻¹A)⁻¹ are defined on p.10 for full column rank
--   - encoding: m unrestricted → m ≥ 2; reason: θ = 1/(10 log m) is undefined at m = 1; this only excludes an undefined case
-- source:
--   Zhang, Wright, A Fast Lewis-weight Interior Point Method for Linear Optimization over Product-Domain (manuscript, sha256 66072000…), Lemma 30, p.25

import Mathlib
import Definitions.Def_BlockLewisIPM_ShortStep

open Matrix MeasureTheory ProbabilityTheory

namespace BlockLewisIPM

open Instance

/-- **Lemma 30**, p.25. Zhang, Wright, *A Fast Lewis-weight Interior Point Method for Linear Optimization
over Product-Domain* (manuscript, sha256 66072000…).

**Formalization Note.** Conventions of `lemma_28`. `T⁻¹δ_τ` is `(δ_{τ,i}/τ_i)_i` with `τ = τ(x)`. -/
theorem lemma_30 (N : ℕ) : ∃ K₀ C₀ : ℝ, 0 < K₀ ∧ 10000 ≤ C₀ ∧ ∀ C ≥ C₀, ∃ Cv₀ : ℝ,
    ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (I : Instance ι), I.Standing N →
    ∀ Cvar ≥ Cv₀,
    ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (R : Ω → ι → ℝ)
      (D : I.StepData), IsStepCall (I.par C) Cvar D μ R →
    let P := I.par C
    let ν := stepLaw P Cvar D μ R
    let τ := I.tau P D.x
    let δτ : Ω → ι → ℝ := fun ω i => D.tauNew P (R ω) i - τ i
    (∀ i, Integrable (fun ω => δτ ω i) ν) ∧
    (∀ i, Integrable (fun ω => ((τ i)⁻¹ * δτ ω i) ^ 2) ν) ∧
    Whp μ P.m (fun ω => supNorm (fun i => (τ i)⁻¹ * δτ ω i) ≤ K₀ * P.β) ∧
    mixedNorm P.Cnorm τ (fun i => ∫ ω, ((τ i)⁻¹ * δτ ω i) ^ 2 ∂ν) ≤ K₀ * P.β ^ 2 ∧
    mixedNorm P.Cnorm τ (fun i => (τ i)⁻¹ * expectVec ν δτ i) ≤
      Real.sqrt (P.p / (2 - P.p)) * P.β + K₀ * ((P.Cnorm⁻¹ + P.α + P.β) * P.β) := by sorry

end BlockLewisIPM
