-- Prove2me | Theorems.Thm_ApproxVI_theorem_2
-- name    : ApproxVI.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:14:23.917494+00:00
-- url     : https://prove2.me/theorems/7471dacc-af75-4925-bb0c-d816b09a7fe5
-- title:
--   Theorem 2 — AVI is a.s. bounded and ends within $\epsilon/(1-\alpha)$ of $J^*$ (corrected: $\limsup\|J_n-J^*\|_\nu\le\epsilon/(1-\alpha)$ replaces convergence into $\{\|TJ-J\|_\nu\le\epsilon\}$)
-- statement:
--   Let $(\Omega,\mathcal F,P)$ be a probability space with a filtration $(\mathcal F_n)_{n\ge0}$. Assume:
--
--   1. **(AV1)** $T:\mathbb R^d\to\mathbb R^d$ satisfies $\|Tx-Ty\|_\nu\le\alpha\|x-y\|_\nu$ for positive weights $\nu$ and some $0<\alpha<1$; $J^*$ is its fixed point;
--   2. **(AV3)** almost surely $\limsup_{n\to\infty}\|\epsilon_n\|_\nu\le\epsilon$ for a fixed $\epsilon>0$;
--   3. **(AV4)** $a(n)\ge0$, $\sum_n a(n)=\infty$, $\sum_n a(n)^2<\infty$;
--   4. **(AV5)** $(M_{n+1})$ is a square-integrable martingale difference sequence, $E[M_{n+1}\mid\mathcal F_n]=0$, with $E[\|M_{n+1}\|^2\mid\mathcal F_n]\le K(1+\|J_n\|^2)$ for some $K>0$;
--   5. on every sample path, $J_{n+1}=J_n+a(n)\big[TJ_n-J_n+\epsilon_n+M_{n+1}\big]$ (5), with $J_0$ and $\epsilon_n$ $\mathcal F_n$-measurable and $M_{n+1}$ $\mathcal F_{n+1}$-measurable.
--
--   Then almost surely AVI is **stable**, $\sup_n\|J_n\|<\infty$, and
--
--   $$
--   \limsup_{n\to\infty}\|J_n-J^*\|_\nu\le\frac{\epsilon}{1-\alpha}.
--   $$
--
--   Here $\|\cdot\|$ is the Euclidean norm. The paper prints a different second conclusion: that $J_n$ converges to some point of $\{J:\|TJ-J\|_\nu\le\epsilon\}$. That claim is false. A two-state discounted Bellman operator with swapped transitions, $\gamma=0.9$, $\epsilon=1$, $a(n)=(n+1)^{-0.51}$, $M\equiv0$ and deterministic errors switching between $(1,1)$ and $(1,-1)$ satisfies (AV1)–(AV5), while $\|TJ_n-J_n\|_\infty\approx1.8>\epsilon$ infinitely often. The radius $\epsilon/(1-\alpha)$ is sharp: for $TJ=J^*+\alpha(J-J^*)$ and constant errors $\epsilon_n\equiv e$ with $\|e\|_\nu\le\epsilon$, $J_n\to J^*+e/(1-\alpha)$.
--
--   The theorem says that approximate value iteration with persistently biased approximations and state-dependent sampling noise does not diverge, and that its asymptotic error is controlled by the approximation error alone.
--
--   **Formalization Note** Each $\limsup\le b$ is written as: for every $\delta>0$, eventually $\le b+\delta$.
--
--   Differences from the source:
--   - correction: (5) converges to an equilibrium point of T̃J − J, i.e., to some point in {J | ‖TJ − J‖_ν ≤ ε} → almost surely limsup_n ‖J_n − J*‖_ν ≤ ε/(1 − α); reason: the printed clause is false: d = 2, TJ = (γJ(2), γJ(1)), γ = 0.9, ν = (1,1), ε = 1, a(n) = (n+1)^(−0.51), M ≡ 0, ε_n = (1,1) if t_n mod 43 < 40 else (1,−1) satisfies (AV1)–(AV5) but ‖TJ_n − J_n‖_∞ ≈ 1.8 > 1 infinitely often; the limsup bound is what the proof's J_n → A′ yields, and its radius is attained
--   - generalization: T is the Bellman operator (3), contractive by (AV1) → T is any map ℝ^d → ℝ^d satisfying (AV1); reason: the argument uses only (AV1); the Bellman operator under (AV1) is an instance
--   - generalization: (AV2): T has a unique fixed point J*, the unique globally asymptotically stable equilibrium of J̇ = TJ − J → not assumed; J* any point with TJ* = J*; reason: (AV1) implies (AV2): Banach's fixed point theorem and ‖J(t) − J*‖_ν ≤ e^{−(1−α)t}‖J(0) − J*‖_ν
--   - generalization: F_n = σ⟨J_m, ε_m | m ≤ n⟩ → any filtration with J_0, ε_n F_n-measurable and M_{n+1} F_{n+1}-measurable; reason: the source's filtration is an instance; adaptedness of J_{n+1} follows from the recursion
--   - encoding: limsup_n x_n ≤ b → ∀ δ > 0, eventually x_n ≤ b + δ; reason: the same condition, without the junk value of a real limsup of an unbounded sequence
--   - encoding: E M²_{n+1} < ∞ and the Euclidean norm ‖·‖ → MemLp (M (n+1)) 2 μ and euclNorm on Fin d → ℝ; reason: Mathlib forms of the same notions; Mathlib's norm on Fin d → ℝ is the sup norm, so the Euclidean norm is explicit
-- source:
--   Ramaswamy & Bhatnagar, Analyzing Approximate Value Iteration Algorithms, arXiv:1709.04673v5, Theorem 2, p.16 (assumptions (AV1)–(AV5), §3.1, p.7; recursion (5), p.6)

import Mathlib
import Definitions.Def_ApproxVI_wNorm
import Definitions.Def_ApproxVI_euclNorm
import Definitions.Def_ApproxVI_IsAVI

namespace ApproxVI

open MeasureTheory Filter

/-- **Theorem 2** (corrected), Ramaswamy & Bhatnagar, *Analyzing Approximate Value Iteration
Algorithms*, arXiv:1709.04673v5, p.16. Under (AV1)–(AV5) (§3.1, p.7) the AVI recursion (5)
(p.6) is stable, `sup_n ‖Jₙ‖ < ∞` a.s., and almost surely
`limsup_n ‖Jₙ − J*‖_ν ≤ ε/(1 − α)`.

The printed convergence clause ("converges to … some point in `{J | ‖TJ − J‖_ν ≤ ε}`") is
false: a two-state discounted Bellman operator with swapped transitions, `γ = 0.9`, `ε = 1`,
`a(n) = (n+1)^{−0.51}`, `M ≡ 0` and errors switching between `(1, 1)` and `(1, −1)` satisfies
(AV1)–(AV5) while `‖TJₙ − Jₙ‖_∞ ≈ 1.8 > ε` infinitely often. The second clause above replaces
it; its radius is attained by `T J = J* + α(J − J*)` with constant errors.

Hypotheses:
* (AV1): `‖Tx − Ty‖_ν ≤ α‖x − y‖_ν`, `0 < α < 1`, weights `νᵢ > 0`; `J*` with `T J* = J*`;
* (AV3): almost surely `limsup ‖εₙ‖_ν ≤ ε` for a fixed `ε > 0`;
* (AV4): `a(n) ≥ 0`, `Σ a(n) = ∞`, `Σ a(n)² < ∞`;
* (AV5): `(Mₙ, ℱₙ)` a square-integrable martingale difference sequence,
  `E[Mₙ₊₁ | ℱₙ] = 0`, `E[‖Mₙ₊₁‖² | ℱₙ] ≤ K(1 + ‖Jₙ‖²)` with `K > 0`;
* the recursion (5) on every sample path, `J₀` and `εₙ` `ℱₙ`-measurable, `Mₙ₊₁`
  `ℱₙ₊₁`-measurable.

**Formalization Note** `ℝ^d` is `Fin d → ℝ`; `‖·‖` is the Euclidean norm `euclNorm`. `T` is
any map satisfying (AV1) (the page's `T` is the Bellman operator (3)); (AV2) is not assumed
because (AV1) implies it. The filtration is any filtration to which the data are adapted (the
page's `ℱₙ = σ⟨J_m, ε_m | m ≤ n⟩` is one; adaptedness of `J_{n+1}` then follows from the
recursion). Each `limsup … ≤ b` is written `∀ δ > 0, eventually … ≤ b + δ`. -/
theorem theorem_2 {d : ℕ} {Ω : Type*} [m₀ : MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m₀)
    (ν : Fin d → ℝ) (hν : ∀ i, 0 < ν i) (α : ℝ) (hα : 0 < α ∧ α < 1)
    (T : (Fin d → ℝ) → (Fin d → ℝ))
    (hT : ∀ x y, wNorm ν (T x - T y) ≤ α * wNorm ν (x - y))
    (Jstar : Fin d → ℝ) (hJstar : T Jstar = Jstar)
    (ε : ℝ) (hε : 0 < ε)
    (a : ℕ → ℝ) (ha_nonneg : ∀ n, 0 ≤ a n)
    (ha_div : Tendsto (fun N => ∑ n ∈ Finset.range N, a n) atTop atTop)
    (ha_sq : Summable fun n => a n ^ 2)
    (J e M : ℕ → Ω → Fin d → ℝ)
    (hAVI : ∀ ω, IsAVI T a (fun n => J n ω) (fun n => e n ω) (fun n => M n ω))
    (hJ0 : StronglyMeasurable[ℱ 0] (J 0))
    (he_adapt : ∀ n, StronglyMeasurable[ℱ n] (e n))
    (hM_adapt : ∀ n, StronglyMeasurable[ℱ (n + 1)] (M (n + 1)))
    (hM_sq : ∀ n, MemLp (M (n + 1)) 2 μ)
    (hM_mds : ∀ n, μ[M (n + 1) | ℱ n] =ᵐ[μ] 0)
    (K : ℝ) (hK : 0 < K)
    (hM_var : ∀ n, μ[fun ω => euclNorm (M (n + 1) ω) ^ 2 | ℱ n]
      ≤ᵐ[μ] fun ω => K * (1 + euclNorm (J n ω) ^ 2))
    (hAV3 : ∀ᵐ ω ∂μ, ∀ δ > 0, ∀ᶠ n in atTop, wNorm ν (e n ω) ≤ ε + δ) :
    ∀ᵐ ω ∂μ, (∃ C : ℝ, ∀ n, euclNorm (J n ω) ≤ C) ∧
      ∀ δ > 0, ∀ᶠ n in atTop, wNorm ν (J n ω - Jstar) ≤ ε / (1 - α) + δ := by sorry

end ApproxVI
