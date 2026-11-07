-- Prove2me | Theorems.Thm_BlockLewisIPM_lemma_38
-- name    : BlockLewisIPM.lemma_38
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:52:31.961989+00:00
-- url     : https://prove2.me/theorems/aebcd9e4-36c4-4563-b087-cc89c406bc26
-- title:
--   Lemma 38 — the block sampling scheme is valid (corrected: $\tau$ overestimates block leverage)
-- statement:
--   Let $\delta\in\mathbb R^n$, let $\bar\tau>0$ overestimate the block leverage scores, $\bar\tau_i\ge c_0\sigma_i(\bar T^{-1/2}\nabla^2\Phi(\bar x)^{-1/2}A)$, for a constant $c_0>0$, and let
--
--   $$p_i=\frac{m}{K\sqrt d}\Bigl(\frac{\|\delta_i\|_2^2}{\|\delta\|_2^2}+\frac1m\Bigr)+\frac{\bar\tau_i}K,\qquad K=\frac{2m}{\sqrt d}+\sum_i\bar\tau_i .$$
--
--   Let $X$ be $e_i/p_i$ with probability $p_i$, and $R=\frac1N\sum_{j=1}^NX^{(j)}$ with $X^{(j)}$ i.i.d. If $N\ge100KC_{\mathrm{Var}}^4\beta^{-2}\log n$, then $\operatorname{diag}_G(R)$ is a valid sampling for $\delta$ in the sense of Definition 19, for $C$ sufficiently large in terms of $c_0$.
--
--   So a sample of size about $\widetilde O(m/\sqrt d+d)$ per step suffices.
--
--   Differences from the source:
--   - correction: τ ∈ ℝ^m_{≥0} arbitrary → τ_i > 0 and τ_i ≥ c₀ σ_i(T^{−1/2}∇²Φ(x̄)^{−1/2}A), C large in terms of c₀; reason: item 5 fails as printed: m = n = d, K_i = [−1,1], ϕ_i = −log(1 − x²), x̄ = 0, A = I, τ_i = 1/d, δ = 1 has K = 2√d + 1, so N < d for large d, and the sampled matrix has rank at most N < d
--   - reading: A any matrix → A of full column rank; reason: P(·) and (A⊤T⁻¹∇²Φ⁻¹A)⁻¹ are defined on p.10 for full column rank
--   - encoding: m unrestricted → m ≥ 2; reason: θ = 1/(10 log m) is undefined at m = 1; this only excludes an undefined case
--   - reading: matrices of Definition 19 item 5 with bars invisible → x̄ ∈ int K and τ̄; reason: Algorithm 1, line 13
--   - reading: ‖δ_i‖²/‖δ‖² at δ = 0 (0/0) → 1/m; reason: so that p stays a probability vector; items 2 and 4 are trivial there
-- source:
--   Zhang, Wright, A Fast Lewis-weight Interior Point Method for Linear Optimization over Product-Domain (manuscript, sha256 66072000…), Lemma 38, p.37, and its proof, pp.76–77

import Mathlib
import Definitions.Def_BlockLewisIPM_ShortStep

open Matrix MeasureTheory ProbabilityTheory

namespace BlockLewisIPM

open Instance

/-- **Lemma 38** (sampling scheme), p.37 (corrected: C3). Zhang, Wright, *A Fast Lewis-weight Interior
Point Method for Linear Optimization over Product-Domain* (manuscript, sha256 66072000…).

**Formalization Note.** C3: `τ̄_i > 0` and `τ̄_i ≥ c₀ σ_i(T̄^{-1/2}∇²Φ(x̄)^{-1/2}A)`, with `A` of full column
rank. As printed `τ ≥ 0` is arbitrary, yet item 5 of Definition 19 is claimed: at `m = n = d`, `A = I`,
`τ_i = 1/d`, `δ = 1` the count `N` is below `d` for large `d`, so the sampled matrix has rank below `d`. The
matrices of Lemma 38 are at `x̄` (bars invisible on the page), as Algorithm 1 uses it. `δ` is the vector of
Definition 19. At `δ = 0` the printed `0/0` is `1/m`. `p` here is the sampling law, not the Lewis exponent. -/
theorem lemma_38 (c₀ : ℝ) (hc₀ : 0 < c₀) : ∃ C₀ : ℝ, 10000 ≤ C₀ ∧ ∀ C ≥ C₀,
    ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (I : Instance ι), I.IsAdmissible →
    2 ≤ Fintype.card ι → FullColRank I.A →
    ∀ (xb : I.Vec) (τb : ι → ℝ) (δ : I.Vec), I.InDomain xb → (∀ i, 0 < τb i) →
    (∀ i, c₀ * blockLeverage I τb xb i ≤ τb i) →
    let P := I.par C
    ∀ Cvar, P.Cnorm ≤ Cvar → ∀ N : ℕ,
    100 * sampleK I τb * Cvar ^ 4 * (P.β ^ 2)⁻¹ * Real.log I.n ≤ N →
    letI : MeasurableSpace (Fin N → ι) := ⊤
    I.IsValidSampling P Cvar xb τb δ (sampleLaw (N := N) (sampleP δ τb))
      (fun idx => sampleR (sampleP δ τb) idx) := by sorry

end BlockLewisIPM
