-- Prove2me | Theorems.Thm_FKZAvg_WStar_theorem_1
-- name    : FKZAvg.WStar.theorem_1
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:35:22.958304+00:00
-- url     : https://prove2.me/theorems/57b6e9cf-48d4-4cc9-a8fe-b3b8650caf8e
-- title:
--   Theorem 1 — under (G), a finite measurable u and stationary φ with (9) give average-cost optimality of φ and (10)
-- statement:
--   Consider a Borel Markov decision process with state space $\mathbb X$, action sets $A(x)$, one-step cost $c$ and transition probability $q$. Let $w(x)$ be the optimal average cost, $w^*=\inf_x w(x)$, $v_\alpha$ the optimal $\alpha$-discounted cost, $m_\alpha=\inf_x v_\alpha(x)$ and $\bar w=\limsup_{\alpha\uparrow1}(1-\alpha)m_\alpha$.
--
--   Assume $w^*<+\infty$ (Assumption (G)). If $u:\mathbb X\to[0,+\infty)$ is measurable and $\phi$ is a stationary policy such that
--
--   $$\bar w+u(x)\ \ge\ c(x,\phi(x))+\int_{\mathbb X}u(y)\,q(dy\mid x,\phi(x)),\qquad x\in\mathbb X,\tag{9}$$
--
--   then $\phi$ is average cost optimal and
--
--   $$w(x)=w^\phi(x)=\limsup_{\alpha\uparrow1}(1-\alpha)v_\alpha(x)=\bar w=w^*,\qquad x\in\mathbb X.\tag{10}$$
--
--   This is the verification step of the paper: it turns an average cost optimality inequality written with $\bar w$ (rather than $\underline w$, as in Schäl's Proposition 1.3) into optimality of the stationary policy.
--
--   **Formalization Note** The state and action spaces are types $\mathbb X$, $\mathbb A$ with a separable metrizable topology whose Borel $\sigma$-algebra is standard Borel; by the Lusin–Souslin theorem these are, up to homeomorphism, exactly the Borel subsets of Polish spaces of the paper. The model is the published `SchalAvg.AvgOpt.Model`: nonempty action sets $A(x)$ with measurable graph $\mathrm{Gr}(A)$, a Markov kernel $q$ on all of $\mathbb X\times\mathbb A$ (only its values on $\mathrm{Gr}(A)$ enter) and a cost $c$ with values in $[0,+\infty]$. The paper's cost is only bounded below; adding a constant to $c$ changes none of the statements (p. 595), so the nonnegative case is the general one. `HasSelector` is the paper's standing assumption (ii) of §2 (a measurable $\phi$ with $\phi(x)\in A(x)$). Optimal values are infima over all admissible (randomized, history-dependent) policies. $u$ is $[0,+\infty]$-valued with the finiteness $u(x)\neq+\infty$ stated for every $x$.
-- source:
--   Feinberg, Kasyanov & Zadoianchuk, Average Cost Markov Decision Processes with Weakly Continuous Transition Probabilities, Math. Oper. Res. 37(4) 2012, p. 594, Theorem 1

import Mathlib
import Definitions.Def_FeinbergLiang_ACOE_MDP
import Definitions.Def_SchalAvg_AvgOpt_Model
import Definitions.Def_FKZAvg_WStar_Assumptions

open scoped ENNReal NNReal Topology
open MeasureTheory ProbabilityTheory Filter SchalAvg.AvgOpt

namespace FKZAvg.WStar

/-- Theorem 1 (p. 594). -/
theorem theorem_1 {X A : Type*}
    [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X] [StandardBorelSpace X]
    [TopologicalSpace A] [TopologicalSpace.MetrizableSpace A] [SecondCountableTopology A]
    [MeasurableSpace A] [BorelSpace A] [StandardBorelSpace A]
    (M : Model X A) (hsel : HasSelector M)
    (hG : GeneralAssumption M) (u : X → ℝ≥0∞) (hu : Measurable u) (hu_fin : ∀ x, u x ≠ ⊤)
    (φ : X → A) (hφ : IsStationary M φ) (h9 : Ineq9 M u φ) :
    IsAvgOpt M hφ ∧ Eq10 M hφ := by sorry

end FKZAvg.WStar
