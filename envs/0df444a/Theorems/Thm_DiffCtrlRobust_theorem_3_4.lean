-- Prove2me | Theorems.Thm_DiffCtrlRobust_theorem_3_4
-- name    : DiffCtrlRobust.theorem_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:51:33.538311+00:00
-- url     : https://prove2.me/theorems/e51cc2a5-9b43-4439-825f-1dfd0d6f4a67
-- title:
--   Theorem 3.4 — discounted-optimal policies of approximate models are asymptotically optimal (corrected: (A5)(ii) one null set, (A5)(iii) uniform in $n$)
-- statement:
--   Let $\alpha>0$, let $\mathbb U$ be a compact metric space, and let $W$ be a $d$-dimensional standard Wiener process. Suppose that $(b,\sigma)$ satisfies (A1)–(A3) and $c\ge0$ satisfies (A4) with bound $M$; that $(b_n,\sigma_n)$ satisfies (A1)–(A3) with the same constants and each $c_n$ is bounded by $M$, jointly continuous and locally Lipschitz in $x$ uniformly in $\zeta$; and that (A5)(i), (ii) hold. Let $v^*_n\in\mathfrak U_{\mathsf{sm}}$ be $\alpha$-discounted optimal for the model $(b_n,\sigma_n,c_n)$ and $v^*\in\mathfrak U_{\mathsf{sm}}$ for the true model $(b,\sigma,c)$. Then
--
--   $$
--   \lim_{n\to\infty}\mathcal J^{v^*_n}_\alpha(x,c)=\mathcal J^{v^*}_\alpha(x,c)\qquad\text{for all }x\in\mathbb R^d,
--   $$
--
--   where $\mathcal J^{v^*_n}_\alpha(x,c)$ is the cost (3.17): the policy $v^*_n$ is run on the true dynamics (2.1) with the true cost.
--
--   A controller who designs an optimal policy for a sufficiently accurate model therefore loses arbitrarily little on the true system.
--
--   **Formalization Note** The statement holds for every choice of the optimal controls and every solution of (2.1) under them; the solutions are unique up to indistinguishability.
--
--   Differences from the source:
--
--   - correction: (A5)(iii): for each n, bₙ and σₙ satisfy (A1)–(A3), constants may depend on n → the same C_R and C₀ for b, σ and all bₙ, σₙ; reason: the literal reading is false: d = 1, U a point, b = bₙ = 0, σ = 1, c = cₙ = 1/(1+x²), σₙ = √(1/n) on [−1/n, 1/n], 1 for |x| ≥ 2/n, linear between; Xⁿ tends to sticky Brownian motion at 0, so Vⁿ_α tends to a function with a kink at 0, not to the C² function V_α; the proof's 'κ₁ independent of n' (p.11) needs the uniform reading
--   - correction: (A5)(ii): for any sequence ζₙ → ζ, convergence for a.e. x, with a null set that may depend on the sequence → one null set: for a.e. x, for every sequence ζₙ → ζ, cₙ(x, ζₙ) → c(x, ζ) and bₙ(x, ζₙ) → b(x, ζ); reason: the sequence-first reading is false: d = 1, U = [0, 1], b = bₙ = 0, σ = σₙ = 1, c = 2 + ζ, cₙ = 2 + ζ − 2φ(n(ζ − g(x))) with φ a smooth bump, φ(0) = 1, supported in [−1, 1], and g(x) = 3/4 + arctan(x)/(2π); for each sequence convergence fails at most at the one x with g(x) = lim ζₙ, all of (A1)–(A5) hold with uniform constants, yet Vⁿ_α(x) stays below 1/α while V_α = 2/α, and every optimal vₙ* has true cost ≥ (5/2 − 1/n)/α against 2/α; the proof uses the x-first form on p.12 ('cₙ(x, ·) → c(x, ·) … continuously on compact set U')
--   - reading: cₙ : ℝᵈ × U → ℝᵈ (p.7) → cₙ real valued with |cₙ| ≤ M, sign not assumed; reason: the printed codomain is a typo: cₙ is a scalar cost compared with c and bounded by M; not assuming cₙ ≥ 0 is the stronger reading
--   - encoding: complete probability space (Ω, 𝔉, ℙ) → any probability space, with the null sets joined to the filtrations explicitly; reason: the filtrations are the same up to null sets and no argument needs more; every complete space is included
--   - encoding: V-valued process U, 𝔘 implicit → jointly measurable U, admissible pairs (U, X) with X adapted to 𝔉; reason: makes 'V valued process' and 'strong solution' precise; the same controls
--   - encoding: optimal: cost equals the value for all x → also requires a solution under v from every x; reason: the clause only excludes vacuous optimality; it holds under (A1)–(A3)
--   - encoding: sup over ζ in (A2) → a bound for every ζ; reason: equivalent for nonempty U
--   - encoding: U a compact metric space, min over U → U also nonempty; reason: a minimum over U presupposes it
--   - encoding: 𝒥 of the (unique) solution X̂ⁿ of (2.1) under v*ₙ → the conclusion for all solutions from x; reason: the solutions exist and are indistinguishable under (A1)–(A3)
-- source:
--   Pradhan & Yüksel, arXiv:2205.05894v2, Theorem 3.4, p.13, (3.17), (3.18)

import Definitions.Def_DiffCtrlRobust_A123
import Definitions.Def_DiffCtrlRobust_CostRegular
import Definitions.Def_DiffCtrlRobust_ModelsConverge
import Definitions.Def_DiffCtrlRobust_IsDiscOptimal
import Definitions.Def_DiffCtrlRobust_UsmTendsto
import Definitions.Def_EthierKurtz_IsStandardBrownian

open MeasureTheory ProbabilityTheory Filter EthierKurtz
open scoped ENNReal NNReal Topology BigOperators

namespace DiffCtrlRobust

/-- Theorem 3.4 (arXiv:2205.05894v2, p.13): under (A1)–(A5), if `v*ₙ ∈ 𝔘sm` is an `α`-discounted
optimal control of the approximating model `(bₙ, σₙ, cₙ)` and `v* ∈ 𝔘sm` of the true model
`(b, σ, c)`, then the true costs converge: `lim_{n→∞} 𝒥^{v*ₙ}_α(x, c) = 𝒥^{v*}_α(x, c)` for all
`x ∈ ℝ^d`, (3.18). Here `𝒥^{v*ₙ}_α(x, c)` is the cost (3.17) of `v*ₙ` on the true dynamics (2.1).

**Formalization Note.** The solutions are quantified universally; `strong_solution_markov` gives one
and identifies all. The hypotheses (A5)(ii), (iii) are corrected as in `theorem_3_3`. Without the
correction of (ii) this theorem fails: in the example of `theorem_3_3`, every minimizing selector
of model `n` is supported in `[g(x) - 1/n, g(x) + 1/n]`, so its true cost is at least
`(5/2 - 1/n) / α`, while the optimal true cost is `2 / α`. -/
theorem theorem_3_4 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {d : ℕ} {U : Type*} [MetricSpace U] [CompactSpace U] [Nonempty U]
    [MeasurableSpace U] [BorelSpace U]
    {W : ℝ≥0 → Ω → SDEState d} (hW : IsStandardBrownian P W)
    {α : ℝ} (hα : 0 < α) {C : ℝ → ℝ} {C₀ M : ℝ} {b : SDEState d → U → SDEState d}
    {σ : SDEState d → SDEDiffusion d} {c : SDEState d → U → ℝ}
    {bs : ℕ → SDEState d → U → SDEState d} {σs : ℕ → SDEState d → SDEDiffusion d}
    {cs : ℕ → SDEState d → U → ℝ}
    (hA : A123 C C₀ b σ) (hc : CostRegular M c) (hc0 : ∀ x ζ, 0 ≤ c x ζ)
    (hAs : ∀ n, A123 C C₀ (bs n) (σs n)) (hcs : ∀ n, CostRegular M (cs n))
    (hconv : ModelsConverge b σ c bs σs cs)
    {vs : ℕ → Usm d U} {v : Usm d U}
    (hvs : ∀ n, IsDiscOptimal P W α (bs n) (σs n) (cs n) (vs n))
    (hv : IsDiscOptimal P W α b σ c v) (x : SDEState d)
    {Xs : ℕ → ℝ≥0 → Ω → SDEState d} {X : ℝ≥0 → Ω → SDEState d}
    (hXs : ∀ n, SolvesMarkov P W b σ (vs n) x (Xs n)) (hX : SolvesMarkov P W b σ v x X) :
    Tendsto (fun n => markovCost P α c (vs n) (Xs n)) atTop (𝓝 (markovCost P α c v X)) := by sorry

end DiffCtrlRobust
