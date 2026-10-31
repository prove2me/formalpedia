-- Prove2me | Theorems.Thm_AdaOGD_theorem_3_7
-- name    : AdaOGD.theorem_3_7
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:21:22.218101+00:00
-- url     : https://prove2.me/theorems/7417751b-aa8f-48ee-86ab-4e5895d85e80
-- title:
--   Theorem 3.7 — MA-AdaOGD: $\mathbb E\|x^T-x^\star\|^2=O(\log^3T/T)$ with an explicit constant
-- statement:
--   Let $\mathcal G$ be a continuous game with $N\ge1$ agents and compact action sets that is $\beta$-strongly monotone ($\beta>0$). Let $G,D>0$ be such that the noisy gradient feedback satisfies $\mathbb E[\xi^t\mid x^t]=v(x^t)$ and $\mathbb E[\|\xi^t\|^2\mid x^t]\le G^2$ for all $t\ge1$, and $\|x-x'\|\le D$ for all $x,x'\in\mathcal X$. If all agents employ Algorithm 3 (MA-AdaOGD) with horizon $T\ge1$, then
--
--   1. $\mathcal G$ has a unique Nash equilibrium $x^\star\in\mathcal X$, and
--   2. $\|x^T-x^\star\|^2$ is integrable and
--   $$
--   \mathbb E\big[\|x^T-x^\star\|^2\big]\ \le\ \frac{D^2}{T}\Big(1+e^{\frac{1}{4\beta^2\log(T+10)}}\Big)\sqrt{1+\log(T+10)+\log(NT)\log(T+10)}
--   +\frac{G^2}{T}\log(T+1)\big(1+\log(T+10)+\log(NT)\log(T+10)\big).
--   $$
--
--   The right-hand side is $O(\log^3(T)/T)$, and the step sizes of the algorithm use neither $\beta$, $G$, $D$ nor $N$: the algorithm is adaptive, and its last iterate converges to the Nash equilibrium at a near-optimal rate.
--
--   **Formalization Note** $\log$ is the natural logarithm. $x^T$ is the iterate after $T-1$ updates, and $T$ is also the horizon in $p_0=1/\log(T+10)$.
--
--   Differences from the source:
--   - reading: $\mathbb E[\xi^t\mid x^t]=v(x^t)$, $\mathbb E[\|\xi^t\|^2\mid x^t]\le G^2$ (p.13) → conditioning on $x^t$ and all step sizes, $\mathcal H_t=\sigma(x^t)\vee\sigma(\{\eta_i^s\}_{1\le i\le N,1\le s\le T})$: $\mathbb E[\xi^t\mid\mathcal H_t]=v(x^t)$, $\mathbb E[\|\xi^t\|^2\mid\mathcal H_t]\le G^2$ a.s., with $\xi^t$ strongly measurable and $\xi^t$, $\|\xi^t\|^2$ integrable, for $1\le t\le T$; reason: the paper's proof (Appendix D, p.40) states exactly this conditioning, "$\{\eta_i^t\}$ are generated independently of any noisy gradient feedback, we have $\mathbb E[(x^\star-x^t)^\top\xi^t\mid x^t,\{\eta_i^t\}]=\mathbb E[(x^\star-x^t)^\top v(x^t)\mid\{\eta_i^t\}]$, $\mathbb E[\|\xi^t\|^2\mid x^t,\{\eta_i^t\}]\le G^2$"; conditioning on $\sigma(x^t)$ alone does not fix the joint law of the noise and the step sizes; the noise may depend on the past beyond $x^t$
--   - reading: Definition 3.1, p.13: each $\mathcal X_i$ convex and bounded → each $\mathcal X_i$ also compact (`IsCompact (G.X i)`); reason: p.1 fixes the action set as convex and compact; closedness is needed for the argmin of Algorithm 3 and for the Nash equilibrium to exist (on $\mathcal X=(0,1)$, $u(x)=(x+1)^2/2$ is $1$-strongly monotone and has no equilibrium)
--   - encoding: $\eta_i^1$ (used in Lemma 3.10, never defined by Algorithm 3) → $\eta_i^1=1$, the formula of line 6 with the empty maximum $0$; reason: the paper's proof holds for any $\eta_i^1$ and the proof of Theorem 3.7 uses $\eta_i^1\le1$
--   - encoding: $x^\star$, the unique Nash equilibrium → every Nash equilibrium $x^\star$; reason: there is exactly one (`nash_exists_unique`), so the statements coincide
--   - encoding: $\mathbb E\|x^T-x^\star\|^2$ → the conclusion also asserts integrability of the integrand; reason: the source takes the expectation as defined; in Lean a non-integrable integrand has integral $0$
--   - encoding: $u_i$ continuously differentiable in $x_i$ with $v_i=\nabla_{x_i}u_i$ (Definition 3.1) → $v_i(x)$ is a gradient of $x_i\mapsto u_i(x_i;x_{-i})$ within $\mathcal X_i$ (`HasGradientWithinAt`), $v$ continuous on $\mathcal X$; each $\mathcal X_i$ nonempty; reason: costs are defined on $\mathcal X$ only, so the derivative is taken within $\mathcal X_i$; nonempty action sets are the standing convention (Algorithm 3 starts from $x_i^1\in\mathcal X_i$)
--   - encoding: agents $\mathcal N=\{1,\dots,N\}$, $x\in\prod_i\mathbb R^{d_i}$ with the Euclidean norm, $\beta$-strongly monotone, rounds $t\ge1$ → agents `Fin N` with $N\ge1$, joint space `PiLp 2` ($\|x\|^2=\sum_i\|x_i\|^2$), $\beta>0$, $T\ge1$; $\max_{1\le i\le N}$ is the real supremum over `Fin N`; reason: Lean conventions; the same instances
--   - encoding: "As a consequence, we have $\mathbb E[\|x^T-x^\star\|^2]=O(\log^3(T)/T)$" → not stated separately; reason: it is a consequence of the explicit bound, which is stated
-- source:
--   Jordan, Lin & Zhou, Adaptive, Doubly Optimal No-Regret Learning in Strongly Monotone and Exp-Concave Games with Gradient Feedback, arXiv:2310.14085v4, Theorem 3.7, p.16

import Mathlib
import Definitions.Def_AdaOGD_IsMAAdaOGDRun

namespace AdaOGD

open MeasureTheory ProbabilityTheory

/-- Theorem 3.7 (Jordan, Lin & Zhou, Adaptive, Doubly Optimal No-Regret Learning in Strongly
Monotone and Exp-Concave Games with Gradient Feedback, arXiv:2310.14085v4, p.16): suppose that a
continuous game is `β`-strongly monotone and let `G, D > 0` satisfy `𝔼[ξᵗ | xᵗ] = v(xᵗ)`,
`𝔼[‖ξᵗ‖² | xᵗ] ≤ G²` for all `t ≥ 1`, and `‖x − x'‖ ≤ D` for all `x, x' ∈ 𝒳`. If all agents
employ Algorithm 3 (MA-AdaOGD), then the game has a unique Nash equilibrium `x⋆ ∈ 𝒳` and
`𝔼[‖xᵀ − x⋆‖²] ≤ D²/T (1 + e^{1/(4β² log(T+10))}) √(1 + log(T + 10) + log(NT) log(T + 10))
  + G²/T log(T + 1) (1 + log(T + 10) + log(NT) log(T + 10))`.

**Formalization Note** Agents are `Fin N` (`N ≥ 1`), rounds are `1, …, T` (`T ≥ 1`), the joint
space is `PiLp 2` (Euclidean norm of the product), `log` is natural. The feedback model is
`IsOracle` (Reading 1: conditioning on `xᵗ` and all step sizes, as in the paper's Appendix D,
p.40); the action sets are compact (p.1);
`η¹ᵢ = 1`. The bound is stated for every Nash equilibrium, which by the first clause is the unique
one. The conclusion asserts integrability of `‖xᵀ − x⋆‖²`, so that `𝔼` is the Bochner integral of
an integrable function. -/
theorem theorem_3_7 {N : ℕ} (hN : 0 < N) {d : Fin N → ℕ} (G : ContinuousGame d)
    (hcompact : ∀ i, IsCompact (G.X i)) {β Gc D : ℝ} (hβ : 0 < β) (hGc : 0 < Gc) (hD : 0 < D)
    (hmono : IsStronglyMonotone G β) (hdiam : DiamLe G D)
    {Ω : Type*} {m0 : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {T : ℕ} (hT : 1 ≤ T)
    {M : Fin N → ℕ → Ω → ℕ} (hM : IsGeomDraws P T M)
    {x1 : Joint d} {ξ x : ℕ → Ω → Joint d} (hξ : IsOracle G P T Gc M x ξ)
    (hx : IsMAAdaOGDRun G T M x1 ξ x) :
    (∃! xs : Joint d, IsNash G xs) ∧
    ∀ xs : Joint d, IsNash G xs →
      Integrable (fun ω => ‖x T ω - xs‖ ^ 2) P ∧
      ∫ ω, ‖x T ω - xs‖ ^ 2 ∂P
        ≤ D ^ 2 / T * (1 + Real.exp (1 / (4 * β ^ 2 * Real.log ((T : ℝ) + 10))))
            * Real.sqrt (1 + Real.log ((T : ℝ) + 10)
                + Real.log ((N : ℝ) * T) * Real.log ((T : ℝ) + 10))
          + Gc ^ 2 / T * Real.log ((T : ℝ) + 1)
            * (1 + Real.log ((T : ℝ) + 10) + Real.log ((N : ℝ) * T) * Real.log ((T : ℝ) + 10)) := by sorry

end AdaOGD
