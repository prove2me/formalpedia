-- Prove2me | Theorems.Thm_FirstOrderOpt_Nonconvex_rsmd_complexity_bound
-- name    : FirstOrderOpt.Nonconvex.rsmd_complexity_bound
-- status  : Disproved
-- author  : @mikedeng1
-- created : 2026-09-19T21:04:05.392458+00:00
-- url     : https://prove2.me/theorems/64a79288-cdb5-4c3a-9755-13a848f1294d
-- title:
--   Theorem 6.6(a) — RSMD complexity bound (goal theorem)
-- statement:
--   The **randomized stochastic mirror descent (RSMD) algorithm**: from $x_1\in X$, at each step
--   $k$ call the stochastic first-order oracle $m_k$ times to form $G_k := \tfrac1{m_k}
--   \sum_{i=1}^{m_k}G(x_k,\xi_{k,i})$ (Eq. (6.2.28)), compute $x_{k+1} := \arg\min_{u\in X}\{
--   \langle G_k,u\rangle + \tfrac1{\gamma_k}V(x_k,u)+h(u)\}$ (Eq. (6.2.29)), and stop at a
--   **randomly chosen** index $R$ with a given pmf $P_R$ on $\{1,\dots,N\}$, outputting $x_R$.
--   **Assumption 13**: for every $k$, $\mathbb{E}[G(x_k,\xi_k)]=\nabla f(x_k)$ and
--   $\mathbb{E}[\|G(x_k,\xi_k)-\nabla f(x_k)\|^2]\le\sigma^2$. Write $\tilde g_{X,k} :=
--   P_X(x_k,G_k,\gamma_k)$ (Eq. (6.2.32)).
--
--   **Theorem 6.6(a).** If $0<\gamma_k\le1/L$ for every $k$ with $\gamma_k<1/L$ for at least one
--   $k$, and $P_R(k) = (\gamma_k-L\gamma_k^2)\big/\sum_{j=1}^N(\gamma_j-L\gamma_j^2)$ (Eq.
--   (6.2.30)), then for any $N\ge1$, under Assumption 13,
--   $$\mathbb{E}\big[\|\tilde g_{X,R}\|^2\big] \le \frac{LD_\Psi^2 + \sigma^2\sum_{k=1}^N(\gamma_k
--   /m_k)}{\sum_{k=1}^N(\gamma_k-L\gamma_k^2)},$$
--   the expectation taken with respect to both $R$ and $\xi_{[N]}:=(\xi_1,\dots,\xi_N)$.
--
--   This is the mission's goal: it shows the RSMD algorithm reaches
--   $\mathbb{E}[\|\tilde g_{X,\bar x}\|^2]\le\varepsilon$ in $O(\sigma^2/\varepsilon^2)$ total
--   calls to the stochastic first-order oracle (choosing $m_k$ and $N$ appropriately, a corollary
--   this mission does not formalize), the stochastic-oracle analogue of `nonconvex_md_rate`'s
--   deterministic $O(1/\varepsilon)$ *iteration* count.
--
--   **Formalization Note.** The book's own proof of this theorem uses a **conditional** form of
--   Assumption 13 — "$\mathbb{E}[\langle\delta_k,g_{X,k}\rangle\mid\xi_{[k-1]}]=0$" — since $x_k$
--   is itself a function of the history $\xi_{[k-1]}$ and hence random from step $2$ on; an
--   unconditional (marginal) mean-zero/variance hypothesis would not suffice to control the
--   cross-terms the proof needs and would misstate the theorem. This is formalized with a
--   Mathlib `Filtration ℕ` `𝒢` (`𝒢 (k-1)` standing for "history through step $k-1$"), `x k` and
--   `G k` required `𝒢 (k-1)`-strongly-measurable, and Assumption 13 stated via
--   `MeasureTheory.condExp (𝒢 (k-1))`: conditional mean `0` and conditional second moment `≤
--   σ²/m_k` for `δ k := G k - ∇f(x k)`. The `σ²/m_k` bound is exactly (6.2.40)'s conclusion for
--   the batch average of `m_k` i.i.d. calls; this mission takes it as the hypothesis on the
--   already-averaged `G k` directly rather than re-deriving it from `m_k` raw calls (that
--   derivation, an application of the pairwise-orthogonal-increments identity for a sum of mean-
--   zero terms, is not itself a numbered milestone of the book and is left out of scope). $R$'s
--   independence from the process $(\tilde g_{X,k})_k$ — used implicitly whenever the book takes
--   the expectation "with respect to $R$ and $\xi_{[N]}$" as $\sum_k P_R(k)\,\mathbb{E}[\|\tilde
--   g_{X,k}\|^2]$ — is stated via `ProbabilityTheory.IndepFun`. Every integrability side
--   condition needed for `condExp`/the Bochner integral in the conclusion to be non-vacuous
--   (rather than silently defaulting to its junk value `0`) is stated as an explicit hypothesis,
--   per `reference/FAITHFULNESS_TRAPS.md` trap 2.
-- source:
--   Lan, First-order and Stochastic Optimization Methods for Machine Learning, Springer 2020, p. 332, Theorem 6.6(a); Assumption 13 at p. 303 (PDF 316)

import Mathlib

namespace FirstOrderOpt.Nonconvex

open scoped RealInnerProductSpace
open MeasureTheory

/-- Theorem 6.6(a) (RSMD complexity bound) — the goal theorem. `Ψ := f + h` on closed convex `X`,
`f` has `L`-Lipschitz gradient `fGrad`. `x k`, `G k` (the batch-averaged stochastic gradient at
step `k`), `xPlus k` (the generalized projection (6.2.6) at `x k` using `G k`) are random
variables on a probability space `(Ω, P)`, adapted to a filtration `𝒢` representing the history
`ξ[k-1]` (`x k`, `G k` are `𝒢 (k-1)`-measurable, matching "`x_k` is a function of the history
`ξ[k-1]`"); `x (k+1) = xPlus k` and `gXtilde k := (1/γ k)•(x k - xPlus k)` is the stochastic
projected gradient `P_X(x k, G k, γ k)` (6.2.32). Assumption 13 is stated conditionally on the
history, matching the book's own `E[⟨δ_k,g_{X,k}⟩ | ξ[k-1]] = 0`: `δ k := G k - fGrad (x k)` has
conditional mean `0` and conditional second moment `≤ σ²/m k` given `𝒢 (k-1)` (the `σ²/m k` bound
is (6.2.40)'s conclusion for the `m k`-sample batch average, taken here directly as the
hypothesis on `G k` rather than re-derived from `m k` raw i.i.d. calls). `R : Ω → ℕ` is a random
stopping index, independent of every `gXtilde k`, supported on `{1,…,N}` with the pmf `PR` of
(6.2.30). Then `E[‖gXtilde_R‖²] ≤ (L·DΨ² + σ²Σ_{k=1}^N(γ k/m k)) / Σ_{k=1}^N(γ k - Lγ k²)`. -/
theorem rsmd_complexity_bound {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    {Ω : Type*} {m0 : MeasurableSpace Ω} (P : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure P] (𝒢 : MeasureTheory.Filtration ℕ m0)
    (X : Set E) (f h : E → ℝ) (V : E → E → ℝ) (L σ : ℝ) (hL : 0 < L) (hσ : 0 ≤ σ)
    (fGrad : E → E)
    (hSmooth : ∀ x ∈ X, ∀ y ∈ X, f y - f x - ⟪fGrad x, y - x⟫ ≤ (L / 2) * ‖y - x‖ ^ 2)
    (N : ℕ) (hN : 1 ≤ N)
    (x1 : E) (hx1 : x1 ∈ X)
    (x G xPlus gXtilde : ℕ → Ω → E) (γ mBatch : ℕ → ℝ)
    (hmBatch : ∀ k, 1 ≤ k → k ≤ N → 0 < mBatch k)
    (hx1def : ∀ ω, x 1 ω = x1)
    (hxMeas : ∀ k, 1 ≤ k → StronglyMeasurable[𝒢 (k - 1)] (x k))
    (hGMeas : ∀ k, 1 ≤ k → StronglyMeasurable[𝒢 (k - 1)] (G k))
    (hx : ∀ k, ∀ ω, x k ω ∈ X) (hxPlusMem : ∀ k, ∀ ω, xPlus k ω ∈ X)
    (hxPlusDef : ∀ k, 1 ≤ k → k ≤ N → ∀ ω, ∀ u ∈ X,
      ⟪G k ω, xPlus k ω⟫ + (1 / γ k) * V (x k ω) (xPlus k ω) + h (xPlus k ω) ≤
        ⟪G k ω, u⟫ + (1 / γ k) * V (x k ω) u + h u)
    (hxNext : ∀ k, 1 ≤ k → k ≤ N → ∀ ω, x (k + 1) ω = xPlus k ω)
    (hgXtilde : ∀ k, 1 ≤ k → k ≤ N → ∀ ω, gXtilde k ω = (1 / γ k) • (x k ω - xPlus k ω))
    (hγpos : ∀ k, 1 ≤ k → k ≤ N → 0 < γ k) (hγub : ∀ k, 1 ≤ k → k ≤ N → γ k ≤ 1 / L)
    (hγstrict : ∃ k, 1 ≤ k ∧ k ≤ N ∧ γ k < 1 / L)
    (hDeltaInt : ∀ k, 1 ≤ k → k ≤ N →
      MeasureTheory.Integrable (fun ω => G k ω - fGrad (x k ω)) P)
    (hDeltaSqInt : ∀ k, 1 ≤ k → k ≤ N →
      MeasureTheory.Integrable (fun ω => ‖G k ω - fGrad (x k ω)‖ ^ 2) P)
    (hUnbiased : ∀ k, 1 ≤ k → k ≤ N →
      MeasureTheory.condExp (𝒢 (k - 1)) P (fun ω => G k ω - fGrad (x k ω)) =ᵐ[P] 0)
    (hVariance : ∀ k, 1 ≤ k → k ≤ N →
      MeasureTheory.condExp (𝒢 (k - 1)) P (fun ω => ‖G k ω - fGrad (x k ω)‖ ^ 2) ≤ᵐ[P]
        (fun _ => σ ^ 2 / mBatch k))
    (ΨStar : ℝ) (hΨStar : IsGLB ((fun x => f x + h x) '' X) ΨStar)
    (DΨ : ℝ) (hDΨ : DΨ = Real.sqrt ((f x1 + h x1 - ΨStar) / L))
    (R : Ω → ℕ) (hRmeas : Measurable R) (hRsupp : ∀ ω, 1 ≤ R ω ∧ R ω ≤ N)
    (PR : ℕ → ℝ)
    (hPR : ∀ k, 1 ≤ k → k ≤ N →
      PR k = (γ k - L * (γ k) ^ 2) / ∑ j ∈ Finset.Icc 1 N, (γ j - L * (γ j) ^ 2))
    (hRlaw : ∀ k, 1 ≤ k → k ≤ N → P {ω | R ω = k} = ENNReal.ofReal (PR k))
    (hRindep : ∀ k, 1 ≤ k → k ≤ N → ProbabilityTheory.IndepFun R (gXtilde k) P)
    (gXtildeR : Ω → E) (hgXtildeR : ∀ ω, gXtildeR ω = gXtilde (R ω) ω)
    (hgXtildeRInt : MeasureTheory.Integrable (fun ω => ‖gXtildeR ω‖ ^ 2) P) :
    ∫ ω, ‖gXtildeR ω‖ ^ 2 ∂P ≤
      (L * DΨ ^ 2 + σ ^ 2 * ∑ k ∈ Finset.Icc 1 N, (γ k / mBatch k)) /
        ∑ k ∈ Finset.Icc 1 N, (γ k - L * (γ k) ^ 2) := by sorry

end FirstOrderOpt.Nonconvex
