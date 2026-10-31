-- Prove2me | Theorems.Thm_AdaOGD_eq_3_4
-- name    : AdaOGD.eq_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:21:10.974017+00:00
-- url     : https://prove2.me/theorems/b3cf7454-1ea6-4e1b-8c83-e50b2867d49d
-- title:
--   Display (3.4) — $T\,\mathbb E\|x^T-x^\star\|^2\le D^2\,\mathrm I+G^2\log(T+1)\,\mathrm{II}+D^2\,\mathrm{III}$
-- statement:
--   Under the hypotheses of Theorem 3.7, compactness aside (a $\beta$-strongly monotone game, the feedback model with $G,D>0$, every agent running Algorithm 3 with horizon $T\ge1$), let $x^\star$ be a Nash equilibrium (there is at most one) and $m^\star=\max_{1\le i\le N,1\le t\le T}M_i^t$. Then $\|x^T-x^\star\|^2$ is integrable and
--   $$
--   T\cdot\mathbb E\big[\|x^T-x^\star\|^2\big]\ \le\ D^2\,\underbrace{\mathbb E\big[\sqrt{1+m^\star}\big]}_{\mathrm I}
--   +G^2\log(T+1)\,\underbrace{\mathbb E\big[1+m^\star\big]}_{\mathrm{II}}
--   +D^2\,\underbrace{\mathbb E\Big[\sum_{t=1}^{T-1}\max\Big\{0,\max_{1\le i\le N}\Big\{\frac{\sqrt{1+m^\star}}{\sqrt{1+\max\{M_i^1,\dots,M_i^t\}}}\Big\}-2\beta\sqrt{1+m^\star}\Big\}\Big]}_{\mathrm{III}} .
--   $$
--
--   The proof of Theorem 3.7 then bounds I, II and III separately; the bounds on I and II are (3.5) and (3.6).
--
--   **Formalization Note** Expectations are Bochner integrals. The three right-hand integrands are nonnegative, so if one were not integrable its integral would be $0$ and the inequality would only be harder.
--
--   Differences from the source:
--   - reading: $\mathbb E[\xi^t\mid x^t]=v(x^t)$, $\mathbb E[\|\xi^t\|^2\mid x^t]\le G^2$ (p.13) → conditioning on $x^t$ and all step sizes, $\mathcal H_t=\sigma(x^t)\vee\sigma(\{\eta_i^s\}_{1\le i\le N,1\le s\le T})$: $\mathbb E[\xi^t\mid\mathcal H_t]=v(x^t)$, $\mathbb E[\|\xi^t\|^2\mid\mathcal H_t]\le G^2$ a.s., with $\xi^t$ strongly measurable and $\xi^t$, $\|\xi^t\|^2$ integrable, for $1\le t\le T$; reason: the paper's proof (Appendix D, p.40) states exactly this conditioning, "$\{\eta_i^t\}$ are generated independently of any noisy gradient feedback, we have $\mathbb E[(x^\star-x^t)^\top\xi^t\mid x^t,\{\eta_i^t\}]=\mathbb E[(x^\star-x^t)^\top v(x^t)\mid\{\eta_i^t\}]$, $\mathbb E[\|\xi^t\|^2\mid x^t,\{\eta_i^t\}]\le G^2$"; conditioning on $\sigma(x^t)$ alone does not fix the joint law of the noise and the step sizes; the noise may depend on the past beyond $x^t$
--   - encoding: $\eta_i^1$ (used in Lemma 3.10, never defined by Algorithm 3) → $\eta_i^1=1$, the formula of line 6 with the empty maximum $0$; reason: the paper's proof holds for any $\eta_i^1$ and the proof of Theorem 3.7 uses $\eta_i^1\le1$
--   - encoding: $x^\star$, the unique Nash equilibrium → every Nash equilibrium $x^\star$; reason: the page's $x^\star$ is a Nash equilibrium; strong monotonicity allows at most one, so the statements coincide
--   - encoding: $\mathbb E\|x^T-x^\star\|^2$ → the conclusion also asserts integrability of the integrand; reason: the source takes the expectation as defined; in Lean a non-integrable integrand has integral $0$
--   - encoding: $u_i$ continuously differentiable in $x_i$ with $v_i=\nabla_{x_i}u_i$ (Definition 3.1) → $v_i(x)$ is a gradient of $x_i\mapsto u_i(x_i;x_{-i})$ within $\mathcal X_i$ (`HasGradientWithinAt`), $v$ continuous on $\mathcal X$; each $\mathcal X_i$ nonempty; reason: costs are defined on $\mathcal X$ only, so the derivative is taken within $\mathcal X_i$; nonempty action sets are the standing convention (Algorithm 3 starts from $x_i^1\in\mathcal X_i$)
--   - encoding: agents $\mathcal N=\{1,\dots,N\}$, $x\in\prod_i\mathbb R^{d_i}$ with the Euclidean norm, $\beta$-strongly monotone, rounds $t\ge1$ → agents `Fin N` with $N\ge1$, joint space `PiLp 2` ($\|x\|^2=\sum_i\|x_i\|^2$), $\beta>0$, $T\ge1$; $\max_{1\le i\le N}$ is the real supremum over `Fin N`; reason: Lean conventions; the same instances
-- source:
--   Jordan, Lin & Zhou, Adaptive, Doubly Optimal No-Regret Learning in Strongly Monotone and Exp-Concave Games with Gradient Feedback, arXiv:2310.14085v4, proof of Theorem 3.7, display (3.4), p.18

import Mathlib
import Definitions.Def_AdaOGD_IsMAAdaOGDRun

namespace AdaOGD

open MeasureTheory ProbabilityTheory

/-- Display (3.4) (Jordan, Lin & Zhou, arXiv:2310.14085v4, proof of Theorem 3.7, display (3.4),
p.18): under the hypotheses of Theorem 3.7, with `m⋆ = max_{1≤i≤N, 1≤t≤T} Mᵗᵢ`,
`T·𝔼[‖xᵀ − x⋆‖²] ≤ D² 𝔼[√(1 + m⋆)] + G² log(T + 1) 𝔼[1 + m⋆]
  + D² 𝔼[∑_{t=1}^{T−1} max{0, max_{1≤i≤N}{√(1 + m⋆)/√(1 + max{M¹ᵢ, …, Mᵗᵢ})} − 2β√(1 + m⋆)}]`
(the three expectations are the terms I, II, III of the paper).

**Formalization Note** Expectations are Bochner integrals. The conclusion asserts integrability of
`‖xᵀ − x⋆‖²`; the right-hand integrands are nonnegative, so a non-integrable one would have
integral `0` and only make the claim stronger. Feedback model: `IsOracle` (Reading 1); `𝒳ᵢ` are
the bounded sets of Definition 3.1, the run and `x⋆` being hypotheses; `η¹ᵢ = 1`; the statement is
for every Nash equilibrium. -/
theorem eq_3_4 {N : ℕ} (hN : 0 < N) {d : Fin N → ℕ} (G : ContinuousGame d)
    {β Gc D : ℝ} (hβ : 0 < β) (hGc : 0 < Gc) (hD : 0 < D)
    (hmono : IsStronglyMonotone G β) (hdiam : DiamLe G D)
    {Ω : Type*} {m0 : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {T : ℕ} (hT : 1 ≤ T)
    {M : Fin N → ℕ → Ω → ℕ} (hM : IsGeomDraws P T M)
    {x1 : Joint d} {ξ x : ℕ → Ω → Joint d} (hξ : IsOracle G P T Gc M x ξ)
    (hx : IsMAAdaOGDRun G T M x1 ξ x)
    (xs : Joint d) (hxs : IsNash G xs) :
    Integrable (fun ω => ‖x T ω - xs‖ ^ 2) P ∧
    (T : ℝ) * ∫ ω, ‖x T ω - xs‖ ^ 2 ∂P
      ≤ D ^ 2 * ∫ ω, Real.sqrt (1 + (maxDraw M T ω : ℝ)) ∂P
        + Gc ^ 2 * Real.log ((T : ℝ) + 1) * ∫ ω, (1 + (maxDraw M T ω : ℝ)) ∂P
        + D ^ 2 * ∫ ω, (∑ t ∈ Finset.Icc 1 (T - 1),
            max 0 ((⨆ i : Fin N, Real.sqrt (1 + (maxDraw M T ω : ℝ))
                      / Real.sqrt (1 + (runMax M i t ω : ℝ)))
                    - 2 * β * Real.sqrt (1 + (maxDraw M T ω : ℝ)))) ∂P := by sorry

end AdaOGD
