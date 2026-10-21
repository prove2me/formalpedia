-- Prove2me | Theorems.Thm_FKZAvg_WStar_lemma_7
-- name    : FKZAvg.WStar.lemma_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:35:35.514682+00:00
-- url     : https://prove2.me/theorems/b725ceaf-b749-40c3-8b8f-e8455abc421f
-- title:
--   Lemma 7 — under (W*) and (B̲), the average cost optimality inequality (31): w̄ + u(x) ≥ min_{a∈A(x)}[c(x,a) + ∫u dq]
-- statement:
--   Consider a Borel Markov decision process with action sets $A(x)$, one-step cost $c$ and transition probability $q$, satisfying Assumptions $(\mathrm W^*)$ and $(\underline{\mathrm B})$. Let $\bar w=\limsup_{\alpha\uparrow1}(1-\alpha)m_\alpha$ and let $u(x)=\liminf_{\alpha\uparrow1,\,y\to x}u_\alpha(y)$ be the function (21). Then for every $x\in\mathbb X$ the minimum below is attained and
--
--   $$\bar w+u(x)\ \ge\ \min_{a\in A(x)}\Big[c(x,a)+\int_{\mathbb X}u(y)\,q(dy\mid x,a)\Big].\tag{31}$$
--
--   This is the average cost optimality inequality from which the stationary optimal policy of Theorem 3 is selected.
--
--   **Formalization Note** The state and action spaces are types $\mathbb X$, $\mathbb A$ with a separable metrizable topology whose Borel $\sigma$-algebra is standard Borel; by the Lusin–Souslin theorem these are, up to homeomorphism, exactly the Borel subsets of Polish spaces of the paper. The model is the published `SchalAvg.AvgOpt.Model`: nonempty action sets $A(x)$ with measurable graph $\mathrm{Gr}(A)$, a Markov kernel $q$ on all of $\mathbb X\times\mathbb A$ (only its values on $\mathrm{Gr}(A)$ enter) and a cost $c$ with values in $[0,+\infty]$. The paper's cost is only bounded below; adding a constant to $c$ changes none of the statements (p. 595), so the nonnegative case is the general one. `HasSelector` is the paper's standing assumption (ii) of §2 (a measurable $\phi$ with $\phi(x)\in A(x)$). Optimal values are infima over all admissible (randomized, history-dependent) policies. \"min\" is stated as: some $a\in A(x)$ attains the infimum $u^*(x)$ of (15) for this $u$, and $u^*(x)\le\bar w+u(x)$.
-- source:
--   Feinberg, Kasyanov & Zadoianchuk, Average Cost Markov Decision Processes with Weakly Continuous Transition Probabilities, Math. Oper. Res. 37(4) 2012, p. 601, Lemma 7

import Mathlib
import Definitions.Def_FeinbergLiang_ACOE_MDP
import Definitions.Def_SchalAvg_AvgOpt_Model
import Definitions.Def_FKZAvg_WStar_Assumptions

open scoped ENNReal NNReal Topology
open MeasureTheory ProbabilityTheory Filter SchalAvg.AvgOpt

namespace FKZAvg.WStar

/-- Lemma 7 (p. 601): (31), with the minimum attained. -/
theorem lemma_7 {X A : Type*}
    [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X] [StandardBorelSpace X]
    [TopologicalSpace A] [TopologicalSpace.MetrizableSpace A] [SecondCountableTopology A]
    [MeasurableSpace A] [BorelSpace A] [StandardBorelSpace A]
    (M : Model X A) (hsel : HasSelector M)
    (hW : CondWStar M) (hB : CondBLow M) :
    ∀ x, (∃ a ∈ M.Aset x, eta M (uAvg M) 1 x a = uStar M (uAvg M) x) ∧
      uStar M (uAvg M) x ≤ gUpper M + uAvg M x := by sorry

end FKZAvg.WStar
