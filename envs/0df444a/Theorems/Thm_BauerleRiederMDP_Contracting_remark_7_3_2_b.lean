-- Prove2me | Theorems.Thm_BauerleRiederMDP_Contracting_remark_7_3_2_b
-- name    : BauerleRiederMDP.Contracting.remark_7_3_2_b
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:28:28.922376+00:00
-- url     : https://prove2.me/theorems/0925cd4b-8abd-4a7d-9c24-d0aecdf58732
-- title:
--   Remark 7.3.2 b) — every contracting model satisfies the Integrability Assumption (A) and the Convergence Assumption (C)
-- statement:
--   Let $(E,A,D,Q,r,\beta)$ be a stationary Markov Decision Model with infinite horizon and let $b:E\to\mathbb R_+$ be a **bounding function**: $b$ is measurable and there are constants $c_r,\alpha_b\ge0$ with
--
--   1. $|r(x,a)|\le c_r\,b(x)$ for all $(x,a)\in D$,
--   2. $\int b(x')\,Q(dx'\mid x,a)\le\alpha_b\,b(x)$ for all $(x,a)\in D$.
--
--   If $\beta\alpha_b<1$ (the model is **contracting**), then the Integrability Assumption (A),
--
--   $$\delta(x)=\sup_\pi\mathbb E^\pi_x\Big[\sum_{k=0}^\infty\beta^kr^+\big(X_k,f_k(X_k)\big)\Big]<\infty\quad\text{for all }x\in E,$$
--
--   and the Convergence Assumption (C),
--
--   $$\lim_{n\to\infty}\sup_\pi\mathbb E^\pi_x\Big[\sum_{k=n}^\infty\beta^kr^+\big(X_k,f_k(X_k)\big)\Big]=0\quad\text{for all }x\in E,$$
--
--   both hold, the suprema taken over Markov policies $\pi\in F^\infty$.
--
--   The remark lets every result of §7.1 proved under (A) and (C), in particular the Structure Theorem 7.1.8, be applied to contracting models.
--
--   **Formalization Note** The model, the bounding function and $\delta$ are the published `MDPFinance.Contracting` bundles; (C) is `ConvergenceAssumptionC`.
--
--   Differences from the source:
--   - encoding: Q a stochastic kernel from D to E and r : D → ℝ → Q a Markov kernel on E × A and r measurable on E × A; reason: only values on D enter any statement, and every kernel and reward on D extend to E × A.
--   - encoding: δ(x) = sup_π 𝔼^π_x[Σ_k β^k r⁺] → sup_π limsup_n of the n-stage expectations of β^k r⁺; reason: the partial sums are nondecreasing, so the limsup is the full expectation (monotone convergence).
--   - encoding: the tail expectation in (C) → full-horizon minus n-stage expectation of β^k r⁺; reason: both are finite under (A), and the difference is the tail.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Springer Universitext, DOI 10.1007/978-3-642-18324-9, Remark 7.3.2 b), p.206 (PDF p.217); Definition 7.3.1, p.205 (PDF p.216)

import Mathlib
import Definitions.Def_MDPFinance_Contracting_Model
import Definitions.Def_MDPFinance_Contracting_Value
import Definitions.Def_MDPFinance_Contracting_Bounding
import Definitions.Def_BauerleRiederMDP_Contracting_ConvergenceAssumptionC

open MeasureTheory ProbabilityTheory Filter Topology

namespace BauerleRiederMDP.Contracting

open MDPFinance.Contracting

/-- **Remark 7.3.2 b)** (Bäuerle & Rieder, *Markov Decision Processes with Applications to
Finance* (2011), Remark 7.3.2 b), p.206, PDF p.217). For any contracting Markov Decision Model,
i.e. one with a bounding function `b` (Definition 7.3.1: `b ≥ 0` measurable,
`|r(x,a)| ≤ c_r b(x)` and `∫ b(x') Q(dx'|x,a) ≤ α_b b(x)` on `D`) and `β α_b < 1`, the
Integrability Assumption (A) and the Convergence Assumption (C) are satisfied.

**Formalization Note.** `IsBoundingFunction M b cr αb` is the published bundle of Definition
7.3.1 with its constants `c_r, α_b ∈ ℝ_+`; (A) is `IntegrabilityAssumptionA` (`δ(x) < ∞` for
all `x`) and (C) is `ConvergenceAssumptionC`. -/
theorem remark_7_3_2_b {E A : Type*} [MeasurableSpace E] [MeasurableSpace A]
    (M : MarkovDecisionModel E A) (b : E → ℝ) (cr αb : ℝ)
    (hb : IsBoundingFunction M b cr αb) (hβαb : M.β * αb < 1) :
    IntegrabilityAssumptionA M ∧ ConvergenceAssumptionC M := by sorry

end BauerleRiederMDP.Contracting
