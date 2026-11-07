-- Prove2me | Theorems.Thm_BlockLewisIPM_lemma_31
-- name    : BlockLewisIPM.lemma_31
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:51:56.527378+00:00
-- url     : https://prove2.me/theorems/873b0e29-a9aa-4531-b355-55251bc0cf45
-- title:
--   Lemma 31 — stability of the residual $\mu$ over one short step
-- statement:
--   Consider one call of Algorithm 1 at an $\epsilon$-centered triplet $(x,s,\rho)$, with an $\alpha$-approximation $(\bar x,\bar\tau)$ of $(x,\tau)$, $\tau=\tau(x)$, and a valid sampling $R$.
--
--   With $\delta_\mu=\mu^{(\mathrm{new})}-\mu$, where $\mu^{(\mathrm{new})}=\mu(x^{(\mathrm{new})},s^{(\mathrm{new})},\rho^{(\mathrm{new})})$, and $g$ of Algorithm 1,
--
--   1. $\|\nabla^2\Phi(x)^{-1/2}\mathbb E[\delta_\mu]-g\|_{2,\tau+\infty}\le\sqrt{p/(2-p)}\,\beta+O((C_{\mathrm{norm}}^{-1}+\alpha+\beta)\beta)$;
--   2. $\bigl\|\bigl(\mathbb E[\|\nabla^2\phi_i(x_i)^{-1/2}\delta_{\mu,i}\|_2^2]\bigr)_i\bigr\|_{\tau+\infty}\lesssim\beta^2$;
--   3. $\|\nabla^2\Phi(x)^{-1/2}\delta_\mu\|_{2,\infty}\lesssim\beta$ with high probability.
--
--   Here $K_0$ is the constant of $\lesssim$ and $O(\cdot)$, which depends only on a bound $N$ on the block sizes. The constant $C$ is sufficiently large, and $C_{\mathrm{Var}}$ is then sufficiently large. Expectations are taken conditionally on the event of items 4 and 5 of Definition 19.
--
--   Differences from the source:
--   - reading: (x̄, τ̄) an α-approximation (the lemma as printed) → also (x, s, ρ) ϵ-centered with the ϵ of Algorithm 1 and all lines of Algorithm 1 hold; reason: §4.2, p.22: "We will suppose (x, s, ρ) is ϵ-central for the rest of the section"
--   - reading: constants hidden in ≲ and O(·), C "sufficiently large" (p.10), C_Var "sufficiently large" (Definition 19) → ∃ K₀ C₀ for each bound N on block sizes, ∀ C ≥ C₀, ∃ a C_Var threshold depending on C only, besides C_Var ≥ C_norm; reason: §3.1 puts C above the hidden constants, Algorithm 1 fixes β without n_i, n_i β ≲ 1 (p.24) needs N, and Definition 19 asks C_Var ≥ C_norm and "a sufficiently large constant"
--   - reading: E[·] → the expectation conditional on the event of Definition 19 items 4 and 5, with integrability stated; reason: x^(new) ∈ int K, and so Ψ, Γ and τ at x^(new), are only known on that event; outside it the terms have junk values
--   - reading: A any matrix → A of full column rank; reason: P(·) and (A⊤T⁻¹∇²Φ⁻¹A)⁻¹ are defined on p.10 for full column rank
--   - encoding: m unrestricted → m ≥ 2; reason: θ = 1/(10 log m) is undefined at m = 1; this only excludes an undefined case
--   - reading: third bullet with no probability → third bullet with high probability; reason: its proof uses the maximum property of R, which is w.h.p.
-- source:
--   Zhang, Wright, A Fast Lewis-weight Interior Point Method for Linear Optimization over Product-Domain (manuscript, sha256 66072000…), Lemma 31, p.25

import Mathlib
import Definitions.Def_BlockLewisIPM_ShortStep

open Matrix MeasureTheory ProbabilityTheory

namespace BlockLewisIPM

open Instance

/-- **Lemma 31**, p.25. Zhang, Wright, *A Fast Lewis-weight Interior Point Method for Linear Optimization
over Product-Domain* (manuscript, sha256 66072000…).

**Formalization Note.** Conventions of `lemma_28`. `µ^(new) = µ(x^(new), s^(new), ρ^(new))`, and `τ^(new)`
in it is `τ(x^(new))`, as printed. The third bullet prints no probability, but its proof gets it w.h.p.,
since `R`'s maximum property is w.h.p. (mission reading). -/
theorem lemma_31 (N : ℕ) : ∃ K₀ C₀ : ℝ, 0 < K₀ ∧ 10000 ≤ C₀ ∧ ∀ C ≥ C₀, ∃ Cv₀ : ℝ,
    ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (I : Instance ι), I.Standing N →
    ∀ Cvar ≥ Cv₀,
    ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (R : Ω → ι → ℝ)
      (D : I.StepData), IsStepCall (I.par C) Cvar D μ R →
    let P := I.par C
    let ν := stepLaw P Cvar D μ R
    let τ := I.tau P D.x
    let μ₀ := I.mu P D.x D.s D.ρ
    let δμ : Ω → I.Vec := fun ω => D.muNew P (R ω) - μ₀
    (∀ j, Integrable (fun ω => δμ ω j) ν) ∧
    (∀ i, Integrable
      (fun ω => eNorm (matInvSqrt (I.hess D.x i) *ᵥ block (δμ ω) i) ^ 2) ν) ∧
    mixedBlockNorm P.Cnorm τ (I.hessInvSqrt D.x *ᵥ expectVec ν δμ - D.g) ≤
      Real.sqrt (P.p / (2 - P.p)) * P.β + K₀ * ((P.Cnorm⁻¹ + P.α + P.β) * P.β) ∧
    mixedNorm P.Cnorm τ
      (fun i => ∫ ω, eNorm (matInvSqrt (I.hess D.x i) *ᵥ block (δμ ω) i) ^ 2 ∂ν) ≤
      K₀ * P.β ^ 2 ∧
    Whp μ P.m (fun ω => blockSupNorm (I.hessInvSqrt D.x *ᵥ δμ ω) ≤ K₀ * P.β) := by sorry

end BlockLewisIPM
