-- Prove2me | Theorems.Thm_DiffCtrlRobust_remark_3_2
-- name    : DiffCtrlRobust.remark_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:49:26.325103+00:00
-- url     : https://prove2.me/theorems/4b0e670f-9268-4c35-b5d8-5c3ac400854f
-- title:
--   Remark 3.2 — the discounted cost is continuous in the policy on $\mathfrak U_{\mathsf{sm}}$
-- statement:
--   Let $\alpha>0$ and suppose (A1)–(A4) hold for the true model. If $v_k\to v$ in $\mathfrak U_{\mathsf{sm}}$, then for every $x\in\mathbb R^d$
--
--   $$
--   \lim_{k\to\infty}\mathcal J^{v_k}_\alpha(x,c)=\mathcal J^{v}_\alpha(x,c).
--   $$
--
--   The dynamics and the cost are those of the true model throughout; only the policy varies.
--
--   Differences from the source:
--
--   - encoding: complete probability space (Ω, 𝔉, ℙ) → any probability space, with the null sets joined to the filtrations explicitly; reason: the filtrations are the same up to null sets and no argument needs more; every complete space is included
--   - encoding: sup over ζ in (A2) → a bound for every ζ; reason: equivalent for nonempty U
--   - encoding: U a compact metric space, min over U → U also nonempty; reason: a minimum over U presupposes it
--   - generalization: the proof treats the optimal controls v*_{n_k} of the approximating models, (3.19)–(3.26) → every convergent sequence in 𝔘sm; reason: the proof does not use optimality at that step and Remark 3.2 claims continuity in the policy; the optimal sequence is a special case
-- source:
--   Pradhan & Yüksel, arXiv:2205.05894v2, Remark 3.2, p.15; shown in (3.19)–(3.26), pp.13–14

import Definitions.Def_DiffCtrlRobust_A123
import Definitions.Def_DiffCtrlRobust_CostRegular
import Definitions.Def_DiffCtrlRobust_SolvesMarkov
import Definitions.Def_DiffCtrlRobust_markovCost
import Definitions.Def_DiffCtrlRobust_UsmTendsto
import Definitions.Def_EthierKurtz_IsStandardBrownian

open MeasureTheory ProbabilityTheory Filter EthierKurtz
open scoped ENNReal NNReal Topology BigOperators

namespace DiffCtrlRobust

/-- Continuity of the cost in the control policy (arXiv:2205.05894v2, Remark 3.2, p.15, shown in
(3.19)–(3.26), pp.13–14): under (A1)–(A4), if `vₖ → v` in `𝔘sm`, then for every `x` the discounted
costs of `vₖ` from `x` converge to the discounted cost of `v` from `x`.

**Formalization Note.** Stated for every convergent sequence in `𝔘sm`, not only for the optimal
controls of the proof, as Remark 3.2 claims. -/
theorem remark_3_2 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {d : ℕ} {U : Type*} [MetricSpace U] [CompactSpace U] [Nonempty U]
    [MeasurableSpace U] [BorelSpace U]
    {W : ℝ≥0 → Ω → SDEState d} (hW : IsStandardBrownian P W)
    {α : ℝ} (hα : 0 < α) {C : ℝ → ℝ} {C₀ M : ℝ} {b : SDEState d → U → SDEState d}
    {σ : SDEState d → SDEDiffusion d} {c : SDEState d → U → ℝ}
    (hA : A123 C C₀ b σ) (hc : CostRegular M c) (hc0 : ∀ x ζ, 0 ≤ c x ζ)
    {vs : ℕ → Usm d U} {v : Usm d U} (hvs : UsmTendsto vs v) (x : SDEState d)
    {Xs : ℕ → ℝ≥0 → Ω → SDEState d} {X : ℝ≥0 → Ω → SDEState d}
    (hXs : ∀ k, SolvesMarkov P W b σ (vs k) x (Xs k)) (hX : SolvesMarkov P W b σ v x X) :
    Tendsto (fun k => markovCost P α c (vs k) (Xs k)) atTop (𝓝 (markovCost P α c v X)) := by sorry

end DiffCtrlRobust
