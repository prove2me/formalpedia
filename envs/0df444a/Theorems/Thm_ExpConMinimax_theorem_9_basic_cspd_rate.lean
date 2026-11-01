-- Prove2me | Theorems.Thm_ExpConMinimax_theorem_9_basic_cspd_rate
-- name    : ExpConMinimax.theorem_9_basic_cspd_rate
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:52:57.896988+00:00
-- url     : https://prove2.me/theorems/0a781032-f245-4a5d-bc87-f7cd8cd6c62e
-- title:
--   Theorem 9 — Basic-CSPD attains $O(1/\sqrt N)$ objective gap and feasibility residuals
-- statement:
--   Consider problem (1.2) under its standing assumptions and Assumptions 2.1 and 2.2, a saddle point $(x^*,y^*,\gamma^*,\lambda^*)$ of (2.1), an initial point $(x_0,y_0,\gamma_0,\lambda_0)\in\mathcal X\times\mathcal Y\times\mathbb R^{m_1}_+\times\mathbb R^{m_2}_+$, and the constant $R$ of (3.13). For $N\ge1$ run Algorithm 1 with i.i.d. oracle samples and step sizes $\eta_t=4\sqrt N C_h^2$, $\kappa_t=4\sqrt N C_g^2$, $\alpha_t=\beta_t=4\sqrt N$, and let $\bar x_N=\frac1N\sum_{t=1}^Nx_t$, $\bar y_N=\frac1N\sum_{t=1}^Ny_t$. Then:
--
--   1. For every random pair $(x,y)$ with values in $\widetilde{\mathcal X}\times\widetilde{\mathcal Y}$ and $\mathbb E\|x\|^2,\mathbb E\|y\|^2<\infty$,
--   $$\mathbb E\big[F(\bar x_N,y)-F(x,\bar y_N)\big]\le\frac1{\sqrt N}\Big(2Re^2+\frac{11C_f^2}{8C_h^2}+2\|\gamma_0\|^2+\frac{\sigma_h^2}8+2C_h^2\mathbb E\|x_0-x\|^2+2C_h^2\mathbb E\|x\|^2\Big)+\frac1{\sqrt N}\Big(\frac{11C_f^2}{8C_g^2}+2\|\lambda_0\|^2+\frac{\sigma_g^2}8+2C_g^2\mathbb E\|y_0-y\|^2+2C_g^2\mathbb E\|y\|^2\Big).$$
--   2. The feasibility residuals satisfy
--   $$\mathbb E\|H(\bar x_N)_+\|_2+\mathbb E\|G(\bar y_N)_+\|_2\le\frac1{\sqrt N}\Big(2Re^2+\frac{11C_f^2}{8C_h^2}+4\|\gamma_0\|^2+\frac{35}8(\|\gamma^*\|+1)^2+(\|\gamma^*\|+1)\sigma_h+\frac{\sigma_h^2}8+2C_h^2\|x_0-x^*\|^2+2C_h^2\|x^*\|^2\Big)$$
--   $$\qquad+\frac1{\sqrt N}\Big(\frac{11C_f^2}{8C_g^2}+4\|\lambda_0\|^2+\frac{35}8(\|\lambda^*\|+1)^2+(\|\lambda^*\|+1)\sigma_g+\frac{\sigma_g^2}8+2C_g^2\|y_0-y^*\|^2+2C_g^2\|y^*\|^2\Big).$$
--   3. There are constants $C_1,C_2>0$, independent of $N$ and of the run, such that for every $N\ge1$ and every run
--   $$-\frac{C_1}{\sqrt N}\le\mathbb E\big[F(\bar x_N,y^*)-F(x^*,\bar y_N)\big]\le\frac{C_2}{\sqrt N} .$$
--
--   All integrands above are integrable. This is the main result of the paper: a projection-based stochastic primal–dual method for convex–concave minimax problems with expectation constraints on both players attains the optimal $O(1/\sqrt N)$ rate for the objective gap and the constraint violation, without assuming bounded dual iterates.
--
--   **Formalization Note** $e=\exp(1)$. In clause 3, $C_1,C_2$ may depend on the problem, the oracle, the constants, the saddle point and the initial point. The probability space carrying the samples is quantified inside each clause.
--
--   Differences from the source:
--   - reading: the γ/x-bracket of the feasibility bound: $\frac{35}8(\|\lambda^*\|+1)^2+(\|\lambda^*\|+1)\sigma_h$ → $\frac{35}8(\|\gamma^*\|+1)^2+(\|\gamma^*\|+1)\sigma_h$; reason: the proof (p.34) applies Theorem 8 with $\|\widetilde\gamma\|=\|\gamma^*\|+1$ and uses $\|\gamma_0-\widetilde\gamma\|^2\le2\|\gamma_0\|^2+2(\|\gamma^*\|+1)^2$; Theorem 16 (p.20) has $\gamma^*$ there; the two readings are incomparable
--   - reading: "Suppose Assumption 2.1 holds" → Assumptions 2.1 and 2.2 and the standing assumptions are hypotheses; reason: §3 assumes Assumptions 2.1 and 2.2 throughout (p.11), and the bounds use the constants $C_h,\sigma_h,C_g,\sigma_g$ of Assumption 2.2
--   - generalization: $F=\mathbb E_\omega f$, $H=\mathbb E_\xi h$, $G=\mathbb E_\zeta g$ → $F$, $H$, $G$ are given functions; $f,h,g$ enter only through the oracle maps, whose means are tied to $F,H,G$ by Assumptions 2.1–2.2; reason: every instance of the paper (with $F:=\mathbb E f$, etc.) is an instance of the Lean statement
--   - generalization: $\widetilde\nabla_xF(x,y)\in\partial_xF(x,y)$, $\widetilde\nabla H(x)\in\partial H(x)$, $\widetilde\nabla G(y)\in\partial G(y)$; convexity of $F(\cdot,y)$, $-F(x,\cdot)$, $H_i$, $G_j$ → subgradient (supergradient for $F(x,\cdot)$) inequalities and convexity required only on $\mathcal X$, resp. $\mathcal Y$; reason: weaker hypotheses: global subgradients and global convexity imply them
--   - generalization: $\mathbb E\|\widetilde\nabla h(x,\xi)\|^2\le C_h^2$ (matrix norm unspecified) → the operator norm of the sampled Jacobian; reason: the operator norm is at most the Frobenius norm, so the hypothesis is weaker and covers both readings
--   - encoding: $\operatorname{argmin}$/$\operatorname{argmax}$ updates of Algorithm 1 → each new iterate is feasible and at least as good as every feasible competitor; reason: the objectives are strongly convex/concave, so this characterizes the unique iterate
--   - encoding: step sizes constant "for all $1\le t\le N$" (resp. $t=1,\dots,N$) → one constant value in every iteration $t\ge 0$; reason: Algorithm 1 iterates $t=0,\dots,N-1$ and the bounds use the same value at $t=0$; constant step sizes are meant
--   - encoding: two independent oracle queries per iteration, independent across iterations → the sample tuples $S_t=(\omega^1_t,\omega^2_t,\xi^1_t,\xi^2_t,\zeta^1_t,\zeta^2_t)$ are independent across $t$, each with law $P_\omega\otimes P_\omega\otimes P_\xi\otimes P_\xi\otimes P_\zeta\otimes P_\zeta$; reason: the paper's sampling model (pp.8, 10)
--   - encoding: oracle outputs are random vectors → the oracle maps are jointly (strongly) measurable in the query point and the sample; reason: needed for the iterates to be random variables; the paper treats them as such
--   - encoding: $\mathbb E[\|\cdot\|^2]<+\infty$ → `MemLp · 2` (measurable and square integrable); reason: a finite second moment presupposes a random variable
--   - encoding: expectations of the bounded quantities → integrability of each integrand is added to the conclusion; reason: so the Bochner integrals are the expectations (no junk value $0$)
-- source:
--   Yang, Li, Lan, Data-Driven Minimax Optimization with Expectation Constraints, arXiv:2202.07868v2, Theorem 9, p.15 (proof App. B.6, pp.33–34)

import Mathlib
import Definitions.Def_ExpConMinimax_Assumption21
import Definitions.Def_ExpConMinimax_Assumption22
import Definitions.Def_ExpConMinimax_IsSaddlePoint
import Definitions.Def_ExpConMinimax_IsRun
import Definitions.Def_ExpConMinimax_SampleModel
import Definitions.Def_ExpConMinimax_Rconst

universe u

namespace ExpConMinimax

open MeasureTheory

/-- **Theorem 9** (Basic-CSPD: `O(1/√N)` rates of the objective gap and feasibility residuals).
Yang, Li, Lan, *Data-Driven Minimax Optimization with Expectation Constraints*,
arXiv:2202.07868v2, Theorem 9, p.15 (Assumptions 2.1 and 2.2 hold throughout §3, p.11):

"Suppose Assumption 2.1 holds. Let `{(xₜ,yₜ,γₜ,λₜ)}` be the sequence generated by Algorithm 1
with `ηₜ = 4√N C_h²`, `κₜ = 4√N C_g²`, and `αₜ = βₜ = 4√N` for all `t = 1,2,⋯,N`. Let `R` be the
constant defined in (3.13). For any `(x,y) ∈ {x ∈ X | H(x) ≤ 0} × {y ∈ Y | G(y) ≤ 0}` satisfying
`E[‖x‖²] < +∞` and `E[‖y‖²] < +∞`, it holds that
`E[F(x̄_N,y) − F(x,ȳ_N)] ≤ 1/√N (2Re² + 11C_f²/(8C_h²) + 2‖γ₀‖² + σ_h²/8 + 2C_h²E[‖x₀ − x‖²]
    + 2C_h²E[‖x‖²]) + 1/√N (11C_f²/(8C_g²) + 2‖λ₀‖² + σ_g²/8 + 2C_g²E[‖y₀ − y‖²] + 2C_g²E[‖y‖²])`
and
`E[‖H(x̄_N)₊‖₂] + E[‖G(ȳ_N)₊‖₂] ≤ 1/√N (2Re² + 11C_f²/(8C_h²) + 4‖γ₀‖² + 35/8(‖λ*‖+1)²
    + (‖λ*‖+1)σ_h + σ_h²/8 + 2C_h²‖x₀ − x*‖² + 2C_h²‖x*‖²) + 1/√N (11C_f²/(8C_g²) + 4‖λ₀‖²
    + 35/8(‖λ*‖+1)² + (‖λ*‖+1)σ_g + σ_g²/8 + 2C_g²‖y₀ − y*‖² + 2C_g²‖y*‖²).
Moreover, there exist constants `C₁, C₂ > 0` such that
`−C₁/√N ≤ E[F(x̄_N,y*) − F(x*,ȳ_N)] ≤ C₂/√N`."

Here `x̄_N = (1/N) ∑_{t=1}^N xₜ`, `ȳ_N = (1/N) ∑_{t=1}^N yₜ` (p.15), `e = Real.exp 1`, `R` is (3.13)
at the saddle point `(x*,y*,γ*,λ*)` of (2.1) and the initial point `(x₀,y₀,γ₀,λ₀)`.

**Reading.** In the first bracket of the feasibility bound the page prints `‖λ*‖`; this
statement has `‖γ*‖` there, as the proof derives it (p.34: "Since `‖λ̃‖ = ‖λ*‖ + 1` and
`‖γ̃‖ = ‖γ*‖ + 1`, it holds from Theorem 8 …", and `‖γ₀ − γ̃‖² ≤ 2‖γ₀‖² + 2(‖γ*‖ + 1)²`).

**Formalization Note.**
1. Assumption 2.2 is a standing assumption of §3 (p.11); the constants `C_h, σ_h, C_g, σ_g`
   of `R` and of the bounds are those of Assumption 2.2.
2. The step sizes are the same in every iteration of the run; the run is on a probability
   space `(Ω, Pr)` carrying the i.i.d. samples (`SampleModel`), the oracle maps are jointly
   measurable, and `Ω` is quantified inside each clause.
3. In the first clause the reference pair `(x, y)` is random: `x(ω) ∈ X̃`, `y(ω) ∈ Ỹ` for every
   `ω`, square integrable (`MemLp · 2`).
4. In the third clause `C₁, C₂ > 0` are chosen before `N`, the probability space and the run;
   they depend only on the problem, the oracle, the constants, the saddle point and the
   initial point.
5. The integrability of each integrand is part of the conclusion, so the Bochner integrals are
   the expectations. `‖·‖₂` is the Euclidean norm and `(·)₊` is `vecPosPart`. -/
theorem theorem_9_basic_cspd_rate {dx dy m₁ m₂ : ℕ} {Sω Sξ Sζ : Type*} [MeasurableSpace Sω]
    [MeasurableSpace Sξ] [MeasurableSpace Sζ] (P : Problem dx dy m₁ m₂)
    (O : Oracle dx dy m₁ m₂ Sω Sξ Sζ) (Cf Ch σh Cg σg : ℝ) (hP : P.Standing)
    (hA21 : Assumption21 P O Cf) (hA22 : Assumption22 P O Ch σh Cg σg)
    (hOm : O.IsMeasurable)
    (xs : Vec dx) (ys : Vec dy) (γs : Vec m₁) (lams : Vec m₂)
    (hsad : IsSaddlePoint P xs ys γs lams)
    (x₀ : Vec dx) (y₀ : Vec dy) (γ₀ : Vec m₁) (lam₀ : Vec m₂) :
    -- Clause 1: objective gap against any random feasible reference pair.
    (∀ N : ℕ, 1 ≤ N → ∀ (Ω : Type u) [MeasurableSpace Ω] (Pr : Measure Ω),
      IsProbabilityMeasure Pr → ∀ S : ℕ → Ω → SampleTuple Sω Sξ Sζ, SampleModel O Pr S →
      ∀ (x : ℕ → Ω → Vec dx) (y : ℕ → Ω → Vec dy) (γ : ℕ → Ω → Vec m₁)
        (lam : ℕ → Ω → Vec m₂),
      IsRun P O S (fun _ => 4 * Real.sqrt N * Ch ^ 2) (fun _ => 4 * Real.sqrt N * Cg ^ 2)
        (fun _ => 4 * Real.sqrt N) (fun _ => 4 * Real.sqrt N) x₀ y₀ γ₀ lam₀ x y γ lam →
      ∀ (u : Ω → Vec dx) (v : Ω → Vec dy), (∀ ω, u ω ∈ P.feasX) → (∀ ω, v ω ∈ P.feasY) →
        MemLp u 2 Pr → MemLp v 2 Pr →
        Integrable (fun ω => P.F (avg N x ω) (v ω) - P.F (u ω) (avg N y ω)) Pr ∧
        ∫ ω, (P.F (avg N x ω) (v ω) - P.F (u ω) (avg N y ω)) ∂Pr ≤
          1 / Real.sqrt N * (2 * Rconst Cf Ch σh Cg σg x₀ y₀ γ₀ lam₀ xs ys γs lams
              * Real.exp 1 ^ 2 + 11 * Cf ^ 2 / (8 * Ch ^ 2) + 2 * ‖γ₀‖ ^ 2 + σh ^ 2 / 8
              + 2 * Ch ^ 2 * ∫ ω, ‖x₀ - u ω‖ ^ 2 ∂Pr + 2 * Ch ^ 2 * ∫ ω, ‖u ω‖ ^ 2 ∂Pr)
          + 1 / Real.sqrt N * (11 * Cf ^ 2 / (8 * Cg ^ 2) + 2 * ‖lam₀‖ ^ 2 + σg ^ 2 / 8
              + 2 * Cg ^ 2 * ∫ ω, ‖y₀ - v ω‖ ^ 2 ∂Pr + 2 * Cg ^ 2 * ∫ ω, ‖v ω‖ ^ 2 ∂Pr)) ∧
    -- Clause 2: feasibility residuals.
    (∀ N : ℕ, 1 ≤ N → ∀ (Ω : Type u) [MeasurableSpace Ω] (Pr : Measure Ω),
      IsProbabilityMeasure Pr → ∀ S : ℕ → Ω → SampleTuple Sω Sξ Sζ, SampleModel O Pr S →
      ∀ (x : ℕ → Ω → Vec dx) (y : ℕ → Ω → Vec dy) (γ : ℕ → Ω → Vec m₁)
        (lam : ℕ → Ω → Vec m₂),
      IsRun P O S (fun _ => 4 * Real.sqrt N * Ch ^ 2) (fun _ => 4 * Real.sqrt N * Cg ^ 2)
        (fun _ => 4 * Real.sqrt N) (fun _ => 4 * Real.sqrt N) x₀ y₀ γ₀ lam₀ x y γ lam →
        Integrable (fun ω => ‖vecPosPart (P.H (avg N x ω))‖) Pr ∧
        Integrable (fun ω => ‖vecPosPart (P.G (avg N y ω))‖) Pr ∧
        ∫ ω, ‖vecPosPart (P.H (avg N x ω))‖ ∂Pr + ∫ ω, ‖vecPosPart (P.G (avg N y ω))‖ ∂Pr ≤
          1 / Real.sqrt N * (2 * Rconst Cf Ch σh Cg σg x₀ y₀ γ₀ lam₀ xs ys γs lams
              * Real.exp 1 ^ 2 + 11 * Cf ^ 2 / (8 * Ch ^ 2) + 4 * ‖γ₀‖ ^ 2
              + 35 / 8 * (‖γs‖ + 1) ^ 2 + (‖γs‖ + 1) * σh + σh ^ 2 / 8
              + 2 * Ch ^ 2 * ‖x₀ - xs‖ ^ 2 + 2 * Ch ^ 2 * ‖xs‖ ^ 2)
          + 1 / Real.sqrt N * (11 * Cf ^ 2 / (8 * Cg ^ 2) + 4 * ‖lam₀‖ ^ 2
              + 35 / 8 * (‖lams‖ + 1) ^ 2 + (‖lams‖ + 1) * σg + σg ^ 2 / 8
              + 2 * Cg ^ 2 * ‖y₀ - ys‖ ^ 2 + 2 * Cg ^ 2 * ‖ys‖ ^ 2)) ∧
    -- Clause 3: two-sided `O(1/√N)` rate of the objective optimality gap.
    (∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧
      ∀ N : ℕ, 1 ≤ N → ∀ (Ω : Type u) [MeasurableSpace Ω] (Pr : Measure Ω),
      IsProbabilityMeasure Pr → ∀ S : ℕ → Ω → SampleTuple Sω Sξ Sζ, SampleModel O Pr S →
      ∀ (x : ℕ → Ω → Vec dx) (y : ℕ → Ω → Vec dy) (γ : ℕ → Ω → Vec m₁)
        (lam : ℕ → Ω → Vec m₂),
      IsRun P O S (fun _ => 4 * Real.sqrt N * Ch ^ 2) (fun _ => 4 * Real.sqrt N * Cg ^ 2)
        (fun _ => 4 * Real.sqrt N) (fun _ => 4 * Real.sqrt N) x₀ y₀ γ₀ lam₀ x y γ lam →
        Integrable (fun ω => P.F (avg N x ω) ys - P.F xs (avg N y ω)) Pr ∧
        -C₁ / Real.sqrt N ≤ ∫ ω, (P.F (avg N x ω) ys - P.F xs (avg N y ω)) ∂Pr ∧
        ∫ ω, (P.F (avg N x ω) ys - P.F xs (avg N y ω)) ∂Pr ≤ C₂ / Real.sqrt N) := by sorry

end ExpConMinimax
