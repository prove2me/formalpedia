-- Prove2me | Theorems.Thm_FKZAvg_WStar_theorem_3
-- name    : FKZAvg.WStar.theorem_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:35:20.940855+00:00
-- url     : https://prove2.me/theorems/a9ea1ab0-b053-44fa-9fbd-2a05463fdc21
-- title:
--   Theorem 3 — under (W*) and (B̲), a stationary φ satisfies (9) with u of (21), (10) holds, and the properties (a)–(e) of u, A*(x) and A_*(x)
-- statement:
--   Consider a discrete-time Markov decision process whose state space $\mathbb X$ and action space $\mathbb A$ are Borel subsets of Polish spaces, with nonempty Borel action sets $A(x)$, Borel graph $\mathrm{Gr}(A)$, a measurable selector of $A$, a bounded below one-step cost $c$ and a transition probability $q$. Let $w(x)$ be the optimal average cost, $w^*=\inf_x w(x)$, $v_\alpha$ the optimal discounted cost, $m_\alpha=\inf_x v_\alpha(x)$, $u_\alpha=v_\alpha-m_\alpha$, $\bar w=\limsup_{\alpha\uparrow1}(1-\alpha)m_\alpha$,
--
--   $$u(x)=\liminf_{\alpha\uparrow1,\,y\to x}u_\alpha(y),\tag{21}$$
--
--   $A^*(x)=\{a\in A(x): \bar w+u(x)\ge c(x,a)+\int u(y)\,q(dy\mid x,a)\}$ (26), and $A_*(x)=\{a\in A(x): c(x,a)+\int u\,dq(\cdot\mid x,a)=\min_{b\in A(x)}[c(x,b)+\int u\,dq(\cdot\mid x,b)]\}$ (17).
--
--   Suppose Assumptions $(\mathrm W^*)$ and $(\underline{\mathrm B})$ hold. Then there is a stationary policy $\phi$ with
--
--   $$\bar w+u(x)\ \ge\ c(x,\phi(x))+\int_{\mathbb X}u(y)\,q(dy\mid x,\phi(x)),\qquad x\in\mathbb X,\tag{9}$$
--
--   and for this $\phi$, $w(x)=w^\phi(x)=\limsup_{\alpha\uparrow1}(1-\alpha)v_\alpha(x)=\bar w=w^*$ for all $x$ (10). Furthermore:
--
--   1. (a) $u$ takes finite nonnegative values and is lower semicontinuous;
--   2. (b) the sets $A^*(x)$ are nonempty, (b₁) $\mathrm{Gr}(A^*)$ is a Borel subset of $\mathbb X\times\mathbb A$, and (b₂) each $A^*(x)$ is compact;
--   3. (c) every stationary policy $\phi$ with $\phi(x)\in A^*(x)$ for all $x$ is average cost optimal and satisfies (9);
--   4. (d) there is a stationary policy $\phi$ with $\phi(x)\in A_*(x)$ for all $x$, and $A_*(x)\subseteq A^*(x)$ for all $x$;
--   5. (e) if, in addition, Assumption $(\mathrm{Wu})$ holds, $u$ is inf-compact.
--
--   This is the main result of the paper: the average cost optimality inequality and a stationary average-cost optimal policy under the weak continuity assumption $(\mathrm W^*)$, which allows noncompact action sets, and the boundedness assumption $(\underline{\mathrm B})$, weaker than Schäl's (B).
--
--   **Formalization Note** The state and action spaces are types $\mathbb X$, $\mathbb A$ with a separable metrizable topology whose Borel $\sigma$-algebra is standard Borel; by the Lusin–Souslin theorem these are, up to homeomorphism, exactly the Borel subsets of Polish spaces of the paper. The model is the published `SchalAvg.AvgOpt.Model`: nonempty action sets $A(x)$ with measurable graph $\mathrm{Gr}(A)$, a Markov kernel $q$ on all of $\mathbb X\times\mathbb A$ (only its values on $\mathrm{Gr}(A)$ enter) and a cost $c$ with values in $[0,+\infty]$. The paper's cost is only bounded below; adding a constant to $c$ changes none of the statements (p. 595), so the nonnegative case is the general one. `HasSelector` is the paper's standing assumption (ii) of §2 (a measurable $\phi$ with $\phi(x)\in A(x)$). Optimal values are infima over all admissible (randomized, history-dependent) policies. Every equality of (10) is stated for every $x$; $u$ is the fixed function (21), never a free parameter; and (W*), (Wu) constrain $c$ and $q$ on $\mathrm{Gr}(A)$ only.
-- source:
--   Feinberg, Kasyanov & Zadoianchuk, Average Cost Markov Decision Processes with Weakly Continuous Transition Probabilities, Math. Oper. Res. 37(4) 2012, p. 600, Theorem 3

import Mathlib
import Definitions.Def_FeinbergLiang_ACOE_MDP
import Definitions.Def_SchalAvg_AvgOpt_Model
import Definitions.Def_FKZAvg_WStar_Assumptions

open scoped ENNReal NNReal Topology
open MeasureTheory ProbabilityTheory Filter SchalAvg.AvgOpt

namespace FKZAvg.WStar

/-- Theorem 3 (p. 600), the main result: all of it. -/
theorem theorem_3 {X A : Type*}
    [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X] [StandardBorelSpace X]
    [TopologicalSpace A] [TopologicalSpace.MetrizableSpace A] [SecondCountableTopology A]
    [MeasurableSpace A] [BorelSpace A] [StandardBorelSpace A]
    (M : Model X A) (hsel : HasSelector M)
    (hW : CondWStar M) (hB : CondBLow M) :
    -- a stationary φ satisfying (9) with u of (21), and (10) for it
    (∃ φ : X → A, ∃ hφ : IsStationary M φ, Ineq9 M (uAvg M) φ ∧ Eq10 M hφ) ∧
    -- (a)
    (LowerSemicontinuous (uAvg M) ∧ ∀ x, uAvg M x ≠ ⊤) ∧
    -- (b): nonempty, (b₁) Borel graph, (b₂) compact
    ((∀ x, (AsupStar M x).Nonempty) ∧
      MeasurableSet {p : X × A | p.2 ∈ AsupStar M p.1} ∧
      ∀ x, IsCompact (AsupStar M x)) ∧
    -- (c)
    (∀ φ : X → A, ∀ hφ : IsStationary M φ, (∀ x, φ x ∈ AsupStar M x) →
      IsAvgOpt M hφ ∧ Ineq9 M (uAvg M) φ) ∧
    -- (d)
    ((∃ φ : X → A, IsStationary M φ ∧ ∀ x, φ x ∈ AsubStar M (uAvg M) x) ∧
      ∀ x, AsubStar M (uAvg M) x ⊆ AsupStar M x) ∧
    -- (e)
    (CondWu M → InfCompactOn (uAvg M) Set.univ) := by sorry

end FKZAvg.WStar
