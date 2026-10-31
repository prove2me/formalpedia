-- Prove2me | Theorems.Thm_DiffCtrlRobust_theorem_3_3
-- name    : DiffCtrlRobust.theorem_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:50:29.179987+00:00
-- url     : https://prove2.me/theorems/d350fb8f-60b8-48a5-a31d-95627778e59f
-- title:
--   Theorem 3.3 — $V^n_\alpha(x)\to V_\alpha(x)$ for all $x$ (corrected: (A5)(ii) one null set, (A5)(iii) uniform in $n$)
-- statement:
--   Let $\alpha>0$. Let $(b,\sigma)$ satisfy (A1)–(A3) and $c\ge0$ satisfy (A4) with bound $M$. Let $(b_n,\sigma_n)$ satisfy (A1)–(A3) with the same constants, let each $c_n$ be bounded by the same $M$, jointly continuous and locally Lipschitz in $x$, and suppose (A5)(i), (ii) hold. Then
--
--   $$
--   \lim_{n\to\infty}V^n_\alpha(x)=V_\alpha(x)\qquad\text{for all }x\in\mathbb R^d.
--   $$
--
--   Both values are infima over all admissible controls, for the same Wiener process on the same probability space. This is the continuity half of the paper's discounted analysis: the optimal value is continuous in the model.
--
--   Differences from the source:
--
--   - correction: (A5)(iii): for each n, bₙ and σₙ satisfy (A1)–(A3), constants may depend on n → the same C_R and C₀ for b, σ and all bₙ, σₙ; reason: the literal reading is false: d = 1, U a point, b = bₙ = 0, σ = 1, c = cₙ = 1/(1+x²), σₙ = √(1/n) on [−1/n, 1/n], 1 for |x| ≥ 2/n, linear between; Xⁿ tends to sticky Brownian motion at 0, so Vⁿ_α tends to a function with a kink at 0, not to the C² function V_α; the proof's 'κ₁ independent of n' (p.11) needs the uniform reading
--   - correction: (A5)(ii): for any sequence ζₙ → ζ, convergence for a.e. x, with a null set that may depend on the sequence → one null set: for a.e. x, for every sequence ζₙ → ζ, cₙ(x, ζₙ) → c(x, ζ) and bₙ(x, ζₙ) → b(x, ζ); reason: the sequence-first reading is false: d = 1, U = [0, 1], b = bₙ = 0, σ = σₙ = 1, c = 2 + ζ, cₙ = 2 + ζ − 2φ(n(ζ − g(x))) with φ a smooth bump, φ(0) = 1, supported in [−1, 1], and g(x) = 3/4 + arctan(x)/(2π); for each sequence convergence fails at most at the one x with g(x) = lim ζₙ, all of (A1)–(A5) hold with uniform constants, yet Vⁿ_α(x) stays below 1/α while V_α = 2/α, and every optimal vₙ* has true cost ≥ (5/2 − 1/n)/α against 2/α; the proof uses the x-first form on p.12 ('cₙ(x, ·) → c(x, ·) … continuously on compact set U')
--   - reading: cₙ : ℝᵈ × U → ℝᵈ (p.7) → cₙ real valued with |cₙ| ≤ M, sign not assumed; reason: the printed codomain is a typo: cₙ is a scalar cost compared with c and bounded by M; not assuming cₙ ≥ 0 is the stronger reading
--   - encoding: complete probability space (Ω, 𝔉, ℙ) → any probability space, with the null sets joined to the filtrations explicitly; reason: the filtrations are the same up to null sets and no argument needs more; every complete space is included
--   - encoding: V-valued process U, 𝔘 implicit → jointly measurable U, admissible pairs (U, X) with X adapted to 𝔉; reason: makes 'V valued process' and 'strong solution' precise; the same controls
--   - encoding: sup over ζ in (A2) → a bound for every ζ; reason: equivalent for nonempty U
--   - encoding: U a compact metric space, min over U → U also nonempty; reason: a minimum over U presupposes it
-- source:
--   Pradhan & Yüksel, arXiv:2205.05894v2, Theorem 3.3, p.11

import Definitions.Def_DiffCtrlRobust_A123
import Definitions.Def_DiffCtrlRobust_CostRegular
import Definitions.Def_DiffCtrlRobust_ModelsConverge
import Definitions.Def_DiffCtrlRobust_value
import Definitions.Def_EthierKurtz_IsStandardBrownian

open MeasureTheory ProbabilityTheory Filter EthierKurtz
open scoped ENNReal NNReal Topology BigOperators

namespace DiffCtrlRobust

/-- Theorem 3.3 (arXiv:2205.05894v2, p.11): under (A1)–(A5), `Vⁿ_α(x) → V_α(x)` for all `x ∈ ℝ^d`,
(3.5). Both values are infima over all admissible controls on the same probability space.

**Formalization Note.** Two corrections of (A5). (iii) The constants `C_R`, `C₀` of (A1)–(A3) are
common to all `n`: otherwise `σₙ = √(1/n)` near `0` gives a sticky limit diffusion and the theorem
fails. (ii) The null set does not depend on the sequence (`ModelsConverge`): otherwise, with `d = 1`,
`U = [0, 1]`, `b = bₙ = 0`, `σ = σₙ = 1`, `c(x, ζ) = 2 + ζ`,
`cₙ(x, ζ) = 2 + ζ - 2 φ(n (ζ - g(x)))`, `φ` a bump with `φ(0) = 1`, and `g` strictly increasing with
values in `(1/2, 1)`, each `cₙ` is admissible and `Vⁿ_α` does not tend to `V_α`. -/
theorem theorem_3_3 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
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
    (x : SDEState d) :
    Tendsto (fun n => value P W α (bs n) (σs n) (cs n) x) atTop
      (𝓝 (value P W α b σ c x)) := by sorry

end DiffCtrlRobust
