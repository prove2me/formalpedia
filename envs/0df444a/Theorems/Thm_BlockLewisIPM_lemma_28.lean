-- Prove2me | Theorems.Thm_BlockLewisIPM_lemma_28
-- name    : BlockLewisIPM.lemma_28
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:52:25.555999+00:00
-- url     : https://prove2.me/theorems/a620e259-9619-4724-a726-1f3b76a79e15
-- title:
--   Lemma 28 — stability of the preconditioner $C$ over one short step
-- statement:
--   Consider one call of Algorithm 1 at an $\epsilon$-centered triplet $(x,s,\rho)$, with an $\alpha$-approximation $(\bar x,\bar\tau)$ of $(x,\tau)$, $\tau=\tau(x)$, and a valid sampling $R$.
--
--   Let $C=\widetilde C(x,\nabla^2\Phi(x))$, $C^{(\mathrm{new})}=\widetilde C(x^{(\mathrm{new})},\nabla^2\Phi(x^{(\mathrm{new})}))$, $\Delta_C=C^{(\mathrm{new})}-C$ and $l_i=\|\operatorname{sym}(C_i^{-1}\Delta_{C,i})\|_{\mathrm{op}}$. Then
--
--   1. $\bigl\|\bigl(\|\mathbb E[\operatorname{sym}(C_i^{-1}\Delta_{C,i})]\|_{\mathrm{op}}\bigr)_i\bigr\|_{\tau+\infty}\le(1+O(\alpha+\beta+C_{\mathrm{norm}}^{-1}))\beta$;
--   2. $\|l\|_\infty\lesssim\beta$ with high probability;
--   3. $\|\mathbb E[l^2]\|_{\tau+\infty}\lesssim\beta^2$.
--
--   Here $K_0$ is the constant of $\lesssim$ and $O(\cdot)$, which depends only on a bound $N$ on the block sizes. The constant $C$ is sufficiently large, and $C_{\mathrm{Var}}$ is then sufficiently large. Expectations are taken conditionally on the event of items 4 and 5 of Definition 19. The statement also records that $x^{(\mathrm{new})}\in\operatorname{int}K$ on that event.
--
--   Differences from the source:
--   - reading: (x̄, τ̄) an α-approximation (the lemma as printed) → also (x, s, ρ) ϵ-centered with the ϵ of Algorithm 1 and all lines of Algorithm 1 hold; reason: §4.2, p.22: "We will suppose (x, s, ρ) is ϵ-central for the rest of the section"
--   - reading: constants hidden in ≲ and O(·), C "sufficiently large" (p.10), C_Var "sufficiently large" (Definition 19) → ∃ K₀ C₀ for each bound N on block sizes, ∀ C ≥ C₀, ∃ a C_Var threshold depending on C only, besides C_Var ≥ C_norm; reason: §3.1 puts C above the hidden constants, Algorithm 1 fixes β without n_i, n_i β ≲ 1 (p.24) needs N, and Definition 19 asks C_Var ≥ C_norm and "a sufficiently large constant"
--   - reading: E[·] → the expectation conditional on the event of Definition 19 items 4 and 5, with integrability stated; reason: x^(new) ∈ int K, and so Ψ, Γ and τ at x^(new), are only known on that event; outside it the terms have junk values
--   - reading: A any matrix → A of full column rank; reason: P(·) and (A⊤T⁻¹∇²Φ⁻¹A)⁻¹ are defined on p.10 for full column rank
--   - encoding: m unrestricted → m ≥ 2; reason: θ = 1/(10 log m) is undefined at m = 1; this only excludes an undefined case
-- source:
--   Zhang, Wright, A Fast Lewis-weight Interior Point Method for Linear Optimization over Product-Domain (manuscript, sha256 66072000…), Lemma 28, p.23

import Mathlib
import Definitions.Def_BlockLewisIPM_ShortStep

open Matrix MeasureTheory ProbabilityTheory

namespace BlockLewisIPM

open Instance

/-- **Lemma 28**, p.23. Zhang, Wright, *A Fast Lewis-weight Interior Point Method for Linear Optimization
over Product-Domain* (manuscript, sha256 66072000…).

**Formalization Note.** Constants: `K₀` is the constant of `≲` and `O(·)`, depending only on the bound
`N` on block sizes (`n_i = O(1)`); then `C` is large (§3.1, p.10); then `C_Var` is at least a
threshold depending on `C` only, besides `C_Var ≥ C_norm` in `IsValidSampling` (Definition 19: "a
sufficiently large constant").
`(x, s, ρ)` is `ϵ`-centered (§4.2, p.22), in `IsStepCall`. `E` is conditional on the good event of
Definition 19's items 4 and 5, the only event where `x^(new) ∈ int K` is known (mission reading);
integrability is stated. `τ` in `‖·‖_{τ+∞}` is `τ(x)`. -/
theorem lemma_28 (N : ℕ) : ∃ K₀ C₀ : ℝ, 0 < K₀ ∧ 10000 ≤ C₀ ∧ ∀ C ≥ C₀, ∃ Cv₀ : ℝ,
    ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (I : Instance ι), I.Standing N →
    ∀ Cvar ≥ Cv₀,
    ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (R : Ω → ι → ℝ)
      (D : I.StepData), IsStepCall (I.par C) Cvar D μ R →
    let P := I.par C
    let ν := stepLaw P Cvar D μ R
    let τ := I.tau P D.x
    let Cold := I.cBlock P.σ D.x
    let E : ∀ i, Ω → Matrix (Fin (I.dim i)) (Fin (I.dim i)) ℝ := fun i ω =>
      sym ((Cold i)⁻¹ * (I.cBlock P.σ (D.xNew (R ω)) i - Cold i))
    let l : ι → Ω → ℝ := fun i ω => opNorm (E i ω)
    (∀ ω, D.GoodStep P Cvar (R ω) → I.InDomain (D.xNew (R ω))) ∧
    (∀ i a b, Integrable (fun ω => E i ω a b) ν) ∧ (∀ i, Integrable (fun ω => l i ω ^ 2) ν) ∧
    mixedNorm P.Cnorm τ (fun i => opNorm (expectMat ν (E i))) ≤
      (1 + K₀ * (P.α + P.β + P.Cnorm⁻¹)) * P.β ∧
    Whp μ P.m (fun ω => supNorm (fun i => l i ω) ≤ K₀ * P.β) ∧
    mixedNorm P.Cnorm τ (fun i => ∫ ω, l i ω ^ 2 ∂ν) ≤ K₀ * P.β ^ 2 := by sorry

end BlockLewisIPM
