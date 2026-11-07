-- Prove2me | Theorems.Thm_BlockLewisIPM_lemma_20
-- name    : BlockLewisIPM.lemma_20
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:52:41.319817+00:00
-- url     : https://prove2.me/theorems/52fe455f-07d3-4bce-962c-c914e69789cb
-- title:
--   Lemma 20 — the potential contracts over one short step
-- statement:
--   Consider one call of Algorithm 1 at an $\epsilon$-centered triplet $(x,s,\rho)$, with an $\alpha$-approximation $(\bar x,\bar\tau)$ of $(x,\tau)$, $\tau=\tau(x)$, and a valid sampling $R$. Let $\rho^{(\mathrm{new})}=(1-r)\rho$ with $r=\alpha\beta/(4C_{\mathrm{norm}}\sqrt d)$. Then
--
--   $$\mathbb E[\Psi(\mu^{(\mathrm{new})},x^{(\mathrm{new})})]\le\Bigl(1-\frac{\theta^2}{20CC_{\mathrm{norm}}C_\lambda\sqrt d}\Bigr)\Psi(\mu,x)+m .$$
--
--   With Markov's inequality this keeps the iterates centered, for $\widetilde O(\sqrt d)$ iterations of the path parameter. The constant $C$ is sufficiently large and $C_{\mathrm{Var}}$ is then sufficiently large. Expectations are taken conditionally on the event of items 4 and 5 of Definition 19.
--
--   Differences from the source:
--   - reading: constants hidden in ≲ and O(·), C "sufficiently large" (p.10), C_Var "sufficiently large" (Definition 19) → ∃ K₀ C₀ for each bound N on block sizes, ∀ C ≥ C₀, ∃ a C_Var threshold depending on C only, besides C_Var ≥ C_norm; reason: §3.1 puts C above the hidden constants, Algorithm 1 fixes β without n_i, n_i β ≲ 1 (p.24) needs N, and Definition 19 asks C_Var ≥ C_norm and "a sufficiently large constant"
--   - reading: E[·] → the expectation conditional on the event of Definition 19 items 4 and 5, with integrability stated; reason: x^(new) ∈ int K, and so Ψ, Γ and τ at x^(new), are only known on that event; outside it the terms have junk values
--   - reading: A any matrix → A of full column rank; reason: P(·) and (A⊤T⁻¹∇²Φ⁻¹A)⁻¹ are defined on p.10 for full column rank
--   - encoding: m unrestricted → m ≥ 2; reason: θ = 1/(10 log m) is undefined at m = 1; this only excludes an undefined case
--   - reading: output of Algorithm 1 at an ϵ-centered triplet → all lines of Algorithm 1 hold, including the assertion with this r; reason: r is unspecified in Algorithm 1; Lemma 20 fixes it
-- source:
--   Zhang, Wright, A Fast Lewis-weight Interior Point Method for Linear Optimization over Product-Domain (manuscript, sha256 66072000…), Lemma 20, p.15

import Mathlib
import Definitions.Def_BlockLewisIPM_ShortStep

open Matrix MeasureTheory ProbabilityTheory

namespace BlockLewisIPM

open Instance

/-- **Lemma 20**, p.15. Zhang, Wright, *A Fast Lewis-weight Interior Point Method for Linear Optimization
over Product-Domain* (manuscript, sha256 66072000…).

**Formalization Note.** Conventions of `lemma_28`; no `≲` occurs, so no `K₀`. `E` is conditional on the
good event of Definition 19's items 4 and 5, and integrability is stated. -/
theorem lemma_20 (N : ℕ) : ∃ C₀ : ℝ, 10000 ≤ C₀ ∧ ∀ C ≥ C₀, ∃ Cv₀ : ℝ,
    ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (I : Instance ι), I.Standing N →
    ∀ Cvar ≥ Cv₀,
    ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (R : Ω → ι → ℝ)
      (D : I.StepData), IsStepCall (I.par C) Cvar D μ R →
    let P := I.par C
    let ν := stepLaw P Cvar D μ R
    D.ρnew = (1 - P.r I.d) * D.ρ →
    Integrable (fun ω => I.Psi P.lam (D.muNew P (R ω)) (D.xNew (R ω))) ν ∧
    ∫ ω, I.Psi P.lam (D.muNew P (R ω)) (D.xNew (R ω)) ∂ν ≤
      (1 - P.θ ^ 2 / (20 * C * P.Cnorm * P.Clam * Real.sqrt I.d)) *
          I.Psi P.lam (I.mu P D.x D.s D.ρ) D.x + Fintype.card ι := by sorry

end BlockLewisIPM
