-- Prove2me | Theorems.Thm_DiffCtrlRobust_limit_policy_optimal
-- name    : DiffCtrlRobust.limit_policy_optimal
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:51:25.279665+00:00
-- url     : https://prove2.me/theorems/fef47dee-370b-4601-b6e2-64d756db38db
-- title:
--   Proof of Theorem 3.4, (3.28)–(3.31) — limits of optimal controls are optimal (corrected: (A5)(ii) one null set, (A5)(iii) uniform in $n$)
-- statement:
--   Under the hypotheses of Theorem 3.4, let $v^*_n$ be $\alpha$-discounted optimal for the approximating model $(b_n,\sigma_n,c_n)$. If a subsequence converges, $v^*_{n_k}\to\hat v$ in $\mathfrak U_{\mathsf{sm}}$, then $\hat v$ is $\alpha$-discounted optimal for the true model $(b,\sigma,c)$.
--
--   The limit policy is optimal for the true model even though no approximating model is the true one. This is the step at which the convergence of the models enters the robustness theorem.
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
-- source:
--   Pradhan & Yüksel, arXiv:2205.05894v2, proof of Theorem 3.4, (3.28)–(3.31), pp.14–15

import Definitions.Def_DiffCtrlRobust_A123
import Definitions.Def_DiffCtrlRobust_CostRegular
import Definitions.Def_DiffCtrlRobust_ModelsConverge
import Definitions.Def_DiffCtrlRobust_IsDiscOptimal
import Definitions.Def_DiffCtrlRobust_UsmTendsto
import Definitions.Def_EthierKurtz_IsStandardBrownian

open MeasureTheory ProbabilityTheory Filter EthierKurtz
open scoped ENNReal NNReal Topology BigOperators

namespace DiffCtrlRobust

/-- Limits of optimal controls are optimal (arXiv:2205.05894v2, proof of Theorem 3.4, (3.28)–(3.31),
pp.14–15): under the hypotheses of Theorem 3.4, if `v_{n_k} → v̂` in `𝔘sm` along a subsequence of
optimal controls of the approximating models, then `v̂` is `α`-discounted optimal for the true model.

**Formalization Note.** The hypotheses (A5)(ii), (iii) are corrected as in `theorem_3_3`. -/
theorem limit_policy_optimal {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
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
    {vs : ℕ → Usm d U} (hvs : ∀ n, IsDiscOptimal P W α (bs n) (σs n) (cs n) (vs n))
    {φ : ℕ → ℕ} (hφ : StrictMono φ) {vhat : Usm d U}
    (hlim : UsmTendsto (fun k => vs (φ k)) vhat) :
    IsDiscOptimal P W α b σ c vhat := by sorry

end DiffCtrlRobust
