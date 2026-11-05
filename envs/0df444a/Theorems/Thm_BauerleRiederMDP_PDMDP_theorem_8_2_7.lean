-- Prove2me | Theorems.Thm_BauerleRiederMDP_PDMDP_theorem_8_2_7
-- name    : BauerleRiederMDP.PDMDP.theorem_8_2_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:34:17.197818+00:00
-- url     : https://prove2.me/theorems/e0d23554-47c6-4b97-aa0b-a88e8d480bce
-- title:
--   Theorem 8.2.7 — Piecewise Deterministic Markov Decision Processes have optimal nonrelaxed Markov policies
-- statement:
--   Let a Piecewise Deterministic Markov Decision Process be given, with state space $E\subset\mathbb R^d$, compact control space $U$, drift $\mu$, flow $\varphi$, jump kernel $Q$, jump rate $\lambda$ and reward rate $r$. Suppose that it has a continuous upper bounding function $b$ with $\alpha_b<1$ and that the continuity and compactness assumptions hold. Suppose moreover that one of the following holds:
--
--   1. $\varphi^\alpha_t(x)$ is independent of $\alpha$ (uncontrolled flow);
--   2. $U$ is convex, $\mu(x,u)$ is linear in $u$ and
--   $$
--   u\mapsto r(x,u)+\lambda\int J^{rel}_\infty(z)\,Q(dz|x,u)
--   $$
--   is concave on $U$.
--
--   Then there exists an optimal nonrelaxed Markov policy $\pi^*=(\pi^*_t)$ with
--   $$
--   \pi^*_t=f(Z_n)(t-T_n),\qquad t\in(T_n,T_{n+1}],
--   $$
--   for a decision rule $f:E\to A$, and $V_\infty=J_\infty=J^{rel}_\infty$. In particular $V_\infty$ is a fixed point of $T$.
--
--   So the continuous-time control problem is solved by a discrete-time Bellman equation on a function space, without differentiability of the value function, and relaxing the controls costs nothing.
--
--   **Formalization Note** $V_\infty$ is the value (8.3) of the continuous-time process; $J_\infty$ and $J^{rel}_\infty$ are the values of the embedded models. Optimality of $f$ is $V_{(f,f,\dots)}=V_\infty$.
--
--   Differences from the source:
--   - encoding: U is a compact Borel subset of a Polish space → U is a nonempty compact metrizable space with its Borel σ-algebra; reason: a compact subset of a Polish space is exactly a compact metrizable space; every theorem here has U compact, and an empty U has no controls, so the book’s action sets are nonempty
--   - encoding: measurable f : E → A, and the book’s remark that it does not distinguish f from a jointly measurable map f̃ : ℝ₊ × E → U → a decision rule is that jointly measurable f̃; reason: this is the book’s own identification, p.245
--   - encoding: the drift μ with no printed measurability → μ is measurable; reason: standing convention of the book, needed for (8.7) to make sense
--   - encoding: value functions in [-∞, ∞) → EReal values, with integrals taken as the difference of the Lebesgue integrals of the positive and the negative part; reason: the bounding function makes the positive parts finite, so no ∞ - ∞ occurs
--   - reading: α_b < 1 → α_b of the embedded model with relaxed controls, the supremum of ∫ b dQ′(·|x,α)/b(x) over x ∈ E and α ∈ R, with 0/0 = 0; reason: the book says b is a bounding function “with and without relaxed controls” and applies Theorem 7.2.1 to the relaxed model; the hypothesis is on α_b itself, not on its bound c_Q c_φ
--   - reading: V_∞ is a fixed point of T → V_∞ = T V_∞ for T the supremum over A (p.249) and for T the supremum over R (p.250); reason: the book gives both forms of T and the proof yields both; the conclusion states both, not the weaker one
--   - reading: φ^α_t(x) is independent of α → independence for α ∈ A; reason: the weaker of the two hypotheses; independence over R follows from it
--   - reading: U is convex, in a Polish space with no named linear structure, and μ(x,u) is linear in u → an embedding ι of U into a Hausdorff locally convex real vector space with convex image, and μ(x,·) continuous; reason: the proof integrates u against α_t(du), which needs a linear structure and continuity of μ(x,·); in ℝ^m a linear or affine map is automatically continuous, so nothing is added there
--   - generalization: μ(x,u) linear in u → μ(x,·) affine along convex combinations in U; reason: a linear map is affine, so the statement specializes to the source’s claim; the proof uses only that μ(x,·) commutes with barycenters
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Theorem 8.2.7, pp.253–254

import Mathlib
import Definitions.Def_BauerleRiederMDP_PDMDP_Model_ConvexLinearConcave
import Definitions.Def_BauerleRiederMDP_PDMDP_JumpModel_ContinuityCompactness
import Definitions.Def_BauerleRiederMDP_PDMDP_JumpModel_IsUpperBounding
import Definitions.Def_BauerleRiederMDP_PDMDP_JumpModel_Vinf
import Definitions.Def_BauerleRiederMDP_PDMDP_JumpModel_relaxedStage
import Definitions.Def_BauerleRiederMDP_PDMDP_Model
import Definitions.Def_BauerleRiederMDP_PDMDP_JumpModel_UncontrolledFlow

namespace BauerleRiederMDP.PDMDP

/-- Theorem 8.2.7 (Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), pp.253–254, PDF 264–265). Suppose the Piecewise Deterministic Markov
Decision Process has a continuous upper bounding function `b` with `α_b < 1` and the continuity
and compactness assumptions are satisfied. If `φ^α_t(x)` is independent of `α` (uncontrolled flow)
or if `U` is convex, `μ(x,u)` is linear in `u` and `u ↦ r(x,u) + λ ∫ J^{rel}_∞(z) Q(dz|x,u)` is
concave on `U`, then there exists an optimal nonrelaxed Markov policy `π*_t = f(Z_n)(t - T_n)`,
`t ∈ (T_n, T_{n+1}]`, for a decision rule `f : E → A`, and `V_∞ = J_∞ = J^{rel}_∞`. In particular
`V_∞` is a fixed point of `T`.

**Formalization Note** `V_∞` is the continuous-time value of (8.3), computed from the law of the
process; `J_∞` and `J^{rel}_∞` are the values of the embedded models. The operator `T` has two forms
in the book, the supremum over `A` (p.249) and over `R` (p.250); the conclusion states both.
`V`, `ι` carry the alternative "`U` convex" (`Model.ConvexLinearConcave`). -/
theorem theorem_8_2_7 {d : ℕ} {E : Set (EuclideanSpace ℝ (Fin d))} {U V : Type*}
    [TopologicalSpace U] [TopologicalSpace.MetrizableSpace U] [MeasurableSpace U] [BorelSpace U]
    [Nonempty U] [AddCommGroup V] [Module ℝ V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [ContinuousSMul ℝ V] [LocallyConvexSpace ℝ V] [T2Space V] (ι : U → V)
    (M : Model E U) (b : E → ℝ) (hb_cont : Continuous b)
    (hb : M.IsUpperBounding b) (hα : M.relaxedStage.alphaB b < 1)
    (hcc : M.ContinuityCompactness b)
    (hcase : M.UncontrolledFlow ∨ M.ConvexLinearConcave ι) :
    ∃ f : DecisionRule E U, (∀ x, M.Vpi (fun _ => f) x = M.Vinf x) ∧
      (∀ x, M.Vinf x = M.Jinf x) ∧ (∀ x, M.Jinf x = M.JinfRelaxed x) ∧
      (∀ x, M.Vinf x = M.stage.T M.Vinf x) ∧
      ∀ x, M.Vinf x = M.relaxedStage.T M.Vinf x := by sorry

end BauerleRiederMDP.PDMDP
