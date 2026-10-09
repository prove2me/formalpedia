-- Prove2me | Theorems.Thm_DynAssortPers_Regret_theorem_6
-- name    : DynAssortPers.Regret.theorem_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T05:17:08.070987+00:00
-- url     : https://prove2.me/theorems/e5beb30b-e0ee-4488-ba43-bdaa8e882f2d
-- title:
--   Theorem 6, p. 24 — $\mathrm{Regret}(T;\pi_{\text{nuc-norm}}(C,\lambda))\le((Cr(m+n)+3)\log T+1)\omega$
-- statement:
--   Consider dynamic assortment personalization with $m\ge1$ customer types, $n\ge1$ items and assortments of at most $K$ items, $1\le K\le n$. Let the revenues satisfy $0\le W_{ij}$ and $\max_{i,j}|W_{ij}|\le\omega$, let the type distribution $\mu^\star$ lie in the simplex $\Delta^m$ with $1/\rho\le m\mu^\star_i\le\rho$ for all $i$ (some $\rho\ge1$), and let the preference matrix satisfy $\operatorname{rank}(\Theta^\star)\le r$ and $\|\Theta^\star\|_\infty\le\alpha/\sqrt{mn}$. Let $\delta>0$ with $\min_i\delta(W_i,\Theta^\star_i;K)\ge\delta$. Choose
--   $$C=\frac{4194304\,K^6\rho^3\omega^2\alpha^2e^{16\alpha}}{\delta^2},\qquad\lambda=8\sqrt{\frac{\rho K}{Crmn}} .\tag{12}$$
--   Then for every way of selecting the estimate $\widehat\Theta$ from the solutions of (5) and the exploited assortment from $S^\star(W_{i_t},\widehat\Theta_{i_t};K)$, Algorithm 2 $\pi_{\text{nuc-norm}}(C,\lambda)$ satisfies
--   $$\mathrm{Regret}(T;\pi_{\text{nuc-norm}}(C,\lambda))\le\big((Cr(m+n)+3)\log T+1\big)\,\omega$$
--   for every integer $T$ with $1\le T\le(m+n)^{mn/(Cr(m+n))}$.
--
--   This is the paper's main regret guarantee for structure-aware dynamic assortment personalization.
--
--   **Formalization Note** Regret is Definition 1 after the tower property (see the Algorithm 2 definition). Added hypotheses, each a necessary reading of the page: $W\ge0$ ($W$ is an expected revenue, and without it a single exploration round can lose more than $\omega$: $n=3$, $K=1$, $W_i=(1,-1,-1)$, large $\Theta^\star_i$, $T=1$); $\delta>0$ (the proof uses $0<\delta\le\delta(W_i,\Theta^\star_i;K)$); $1\le K\le n$ (exploration draws a subset of size exactly $K$); $m,n\ge1$; $T\ge1$. The gap hypothesis is the "for every non-optimal assortment" form, vacuous for a type at which every assortment is optimal. **Horizon:** the page prints $T\le(m+n)^{\frac{mn}{C(m+n)}r}$; the statement uses the exponent $mn/(Cr(m+n))$, which is what the proof's application of Theorem 3 requires ($Cr(m+n)\log t\le mn\log(m+n)$); for $r\ge1$ this is the smaller range, so the claim is weaker than the literal reading. If $r=0$ (so $\Theta^\star=0$), Lean's $x/0=0$ makes $\lambda=0$ and the horizon $T\le1$. The estimator is any map returning a solution of (5) on every nonempty sample and the exploitation rule any map returning an optimal assortment; both are quantified universally. Types and items are 0-based.
-- source:
--   Kallus, Udell, Dynamic Assortment Personalization in High Dimensions, arXiv:1610.05604 (PDF sha256 2b010481…216a), Theorem 6, eq. (12), p. 24 (proof pp. 46–48); Algorithm 2, p. 23; Definition 1, p. 6

import Mathlib
import Definitions.Def_DynAssortPers_Regret_Algorithm2

namespace DynAssortPers.Regret

open MatrixCompletion

/-- Theorem 6 (p. 24). Let `m, n ≥ 1`, `1 ≤ K ≤ n`, revenues `W ≥ 0` with `‖W‖_∞ ≤ ω`, a type
distribution `μ⋆ ∈ Δ^m` with `1/ρ ≤ m μ⋆_i ≤ ρ` (`ρ ≥ 1`), and `Θ⋆` with `rank Θ⋆ ≤ r`,
`‖Θ⋆‖_∞ ≤ α/√(mn)` and `min_i δ(W_i, Θ⋆_i; K) ≥ δ > 0`. With
`C = 4194304 K⁶ ρ³ ω² α² e^{16α} / δ²` and `λ = 8 √(ρK/(Crmn))` (12), for every selection `est` from
the argmin of (5) and every selection `exploit` of optimal assortments, Algorithm 2 has
`Regret(T) ≤ ((C r (m + n) + 3) log T + 1) ω` for all `1 ≤ T ≤ (m + n)^{mn/(C r (m + n))}`. -/
theorem theorem_6 (m n K : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) (hK : 1 ≤ K) (hKn : K ≤ n)
    (W : RealMatrix m n) (hW : ∀ i j, 0 ≤ W i j) (ω : ℝ) (hω : entrySupNorm W ≤ ω)
    (μ : Fin m → ℝ) (hμ0 : ∀ i, 0 ≤ μ i) (hμ1 : ∑ i, μ i = 1)
    (Θs : RealMatrix m n) (r : ℕ) (hr : Θs.rank ≤ r)
    (ρ : ℝ) (hρ : 1 ≤ ρ) (hρμ : ∀ i, 1 / ρ ≤ (m : ℝ) * μ i ∧ (m : ℝ) * μ i ≤ ρ)
    (α : ℝ) (hα : entrySupNorm Θs ≤ α / Real.sqrt ((m : ℝ) * n))
    (δ : ℝ) (hδ : 0 < δ) (hgap : ∀ i, HasGap (W i) (Θs i) K δ)
    (C lam : ℝ)
    (hC : C = 4194304 * (K : ℝ) ^ 6 * ρ ^ 3 * ω ^ 2 * α ^ 2 * Real.exp (16 * α) / δ ^ 2)
    (hlam : lam = 8 * Real.sqrt (ρ * K / (C * r * m * n)))
    (est : List (Obs m n) → RealMatrix m n) (hest : ∀ O, O ≠ [] → IsEstimate O lam α (est O))
    (exploit : Fin m → RealMatrix m n → Finset (Fin n))
    (hexploit : ∀ i Θ, IsOptimal (W i) (Θ i) K (exploit i Θ))
    (T : ℕ) (hT1 : 1 ≤ T)
    (hT : (T : ℝ) ≤ ((m : ℝ) + n) ^ ((m : ℝ) * n / (C * r * ((m : ℝ) + n)))) :
    alg2Regret W μ Θs K C r est exploit T ≤
      ((C * r * ((m : ℝ) + n) + 3) * Real.log T + 1) * ω := by sorry

end DynAssortPers.Regret
