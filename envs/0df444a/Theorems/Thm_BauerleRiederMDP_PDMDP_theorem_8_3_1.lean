-- Prove2me | Theorems.Thm_BauerleRiederMDP_PDMDP_theorem_8_3_1
-- name    : BauerleRiederMDP.PDMDP.theorem_8_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:33:35.913362+00:00
-- url     : https://prove2.me/theorems/37adaf3e-9bee-41be-8b01-9d7ee53f13b2
-- title:
--   Theorem 8.3.1 — the infinite-horizon chain: $V_\infty$ solves (8.10) and a stationary maximizer is optimal
-- statement:
--   Let a continuous-time Markov Decision Chain be given, with countable state space $E$, rates $q_{xy}(u)$, uniformization rate $\lambda$, reward rate $r$ and discount rate $\beta\ge0$. Suppose that it has an upper bounding function $b$ with $\alpha_b<1$ and that
--
--   1. $U$ is compact,
--   2. $u\mapsto q_{xy}(u)$ is continuous for all $x,y\in E$,
--   3. $u\mapsto\sum_{y\in E}b(y)q_{xy}(u)$ is continuous for all $x\in E$,
--   4. $u\mapsto r(x,u)$ is upper semicontinuous for all $x\in E$.
--
--   Then $V_\infty\in\mathbb B_b^+$, $V_\infty$ is a fixed point of $T$, that is,
--   $$
--   \beta V_\infty(x)=\sup_{u\in U}\Big\{r(x,u)+\sum_{y\in E}q_{xy}(u)V_\infty(y)\Big\},\qquad x\in E,\tag{8.10}
--   $$
--   and there exists an optimal Markov policy $\pi^*_t=f^*(X_{t-})$, $t\ge0$, for a decision rule $f^*:E\to U$, where $f^*(x)$ is a maximum point of $u\mapsto r(x,u)+\sum_{y\in E}q_{xy}(u)V_\infty(y)$.
--
--   Equation (8.10) coincides with the Hamilton–Jacobi–Bellman equation of the chain, so the theorem solves the control problem for a controlled continuous-time Markov chain with bounded rates.
--
--   **Formalization Note** $V_\infty$ is the continuous-time value over all Markov policies $f_n:E\to A$, computed from the law of the process.
--
--   Differences from the source:
--   - encoding: U is a compact Borel subset of a Polish space → U is a nonempty compact metrizable space with its Borel σ-algebra; reason: a compact subset of a Polish space is exactly a compact metrizable space; every theorem here has U compact, and an empty U has no controls, so the book’s action sets are nonempty
--   - encoding: value functions in [-∞, ∞) → EReal values, with integrals taken as the difference of the Lebesgue integrals of the positive and the negative part; reason: the bounding function makes the positive parts finite, so no ∞ - ∞ occurs
--   - encoding: (8.10) and the maximum-point property at every x ∈ E → V_∞ = T V_∞ at every x, with T in the form with Q; (8.10) and the maximum-point property at every x with V_∞(x) > -∞; reason: at V_∞(x) = -∞ the term q_{xx}(u)V_∞(x) makes the display of the form ∞ - ∞ (and β V_∞(x) of the form 0·∞ if β = 0); on those states the form with Q gives the same information and every u is a maximum point of it
--   - encoding: rates q_{xy}(u) ∈ ℝ → q_{xy}(u) ≥ 0 for y ≠ x and q_{xy} measurable in u; reason: these make Q a stochastic kernel, which the book’s construction requires
--   - encoding: E countable → E countable with the discrete topology and σ-algebra; reason: the standard structure of a countable state space
--   - reading: α_b < 1 → α_b of the model (E, U, Q′, r′), the supremum over (x, u); reason: this is the embedded model the book writes for the chain, p.257
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Theorem 8.3.1, pp.257–258

import Mathlib
import Definitions.Def_BauerleRiederMDP_PDMDP_Chain
import Definitions.Def_BauerleRiederMDP_PDMDP_JumpModel_IsUpperBounding
import Definitions.Def_BauerleRiederMDP_PDMDP_JumpModel_Vinf
import Definitions.Def_MDPFinance_PDMDP_Core

open MDPFinance.PDMDP (IBbPlus)

namespace BauerleRiederMDP.PDMDP

/-- Theorem 8.3.1 (Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), pp.257–258, PDF 268–269). Suppose the continuous-time Markov Decision
Chain has an upper bounding function `b` with `α_b < 1` and the continuity and compactness
assumptions (i)–(iv) are satisfied. Then
a) `V_∞ ∈ IB_b^+` and `V_∞` is a fixed point of `T`, i.e.
`β V_∞(x) = sup_u {r(x,u) + ∑_y q_{xy}(u) V_∞(y)}`, `x ∈ E` (8.10);
b) there exists an optimal Markov policy `π*_t = f*(X_{t-})`, `t ≥ 0`, for a decision rule
`f* : E → U`, where `f*(x)` is a maximum point of `u ↦ r(x,u) + ∑_y q_{xy}(u) V_∞(y)`.

**Formalization Note** `V_∞` is the continuous-time value over all Markov policies `f_n : E → A`,
computed from the law of the process. Its values lie in `[-∞, ∞)`. The fixed-point equation
`V_∞ = T V_∞` holds at every `x`; (8.10) and the maximum-point property are stated where
`V_∞(x) > -∞`, because at `V_∞(x) = -∞` the term `q_{xx}(u) V_∞(x)` of the sum makes the display
of the form `∞ - ∞` (and `β V_∞(x)` of the form `0 · ∞` when `β = 0`). `E` is discrete. `α_b` is
that of the model `(E, U, Q', r')`. -/
theorem theorem_8_3_1 {E U : Type*} [TopologicalSpace E] [DiscreteTopology E] [Countable E]
    [MeasurableSpace E] [BorelSpace E] [TopologicalSpace U] [TopologicalSpace.MetrizableSpace U]
    [MeasurableSpace U] [BorelSpace U] [Nonempty U] (C : Chain E U) (b : E → ℝ)
    (hb : C.toJump.IsUpperBounding b) (hα : C.stage.alphaB b < 1)
    (hcc : C.toRateModel.ContinuityCompactness b) :
    (C.toJump.Vinf ∈ IBbPlus b ∧ (∀ x, C.toJump.Vinf x = C.stage.T C.toJump.Vinf x) ∧
        ∀ x, C.toJump.Vinf x ≠ ⊥ →
          (C.β : EReal) * C.toJump.Vinf x = ⨆ u, C.rateObjective C.toJump.Vinf x u) ∧
      ∃ (fs : E → U) (hfs : Measurable fs),
        (∀ x, C.toJump.Vinf x ≠ ⊥ →
          ∀ u, C.rateObjective C.toJump.Vinf x u ≤ C.rateObjective C.toJump.Vinf x (fs x)) ∧
        ∀ x, C.toJump.Vpi (fun _ => stationaryRule fs hfs) x = C.toJump.Vinf x := by sorry

end BauerleRiederMDP.PDMDP
