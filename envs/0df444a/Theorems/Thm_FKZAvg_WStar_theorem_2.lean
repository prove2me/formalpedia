-- Prove2me | Theorems.Thm_FKZAvg_WStar_theorem_2
-- name    : FKZAvg.WStar.theorem_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:35:26.6529+00:00
-- url     : https://prove2.me/theorems/caa901b6-eb48-4c25-a956-a32cfea4e24d
-- title:
--   Theorem 2 (i), (iv)–(vi) — under (W*): lower semicontinuity and convergence of values, the discounted optimality equation (20), A_α, stationary optimal policies
-- statement:
--   Consider a Borel Markov decision process with action sets $A(x)$, one-step cost $c$ and transition probability $q$, satisfying Assumption $(\mathrm W^*)$, and fix a discount factor $\alpha\in[0,1)$. Let $v_{n,\alpha}$ be the optimal $n$-horizon discounted cost ($v_{0,\alpha}=0$) and $v_\alpha$ the optimal infinite-horizon discounted cost. Then:
--
--   1. (i) the functions $v_{n,\alpha}$, $n=0,1,2,\dots$, and $v_\alpha$ are lower semicontinuous on $\mathbb X$, and $v_{n,\alpha}(x)\to v_\alpha(x)$ as $n\to\infty$ for every $x$;
--   2. (iv) $v_\alpha$ satisfies
--   $$v_\alpha(x)=\min_{a\in A(x)}\Big\{c(x,a)+\alpha\int_{\mathbb X}v_\alpha(y)\,q(dy\mid x,a)\Big\},\qquad x\in\mathbb X,\tag{20}$$
--   the minimum being attained, so the sets $A_\alpha(x)=\{a\in A(x): v_\alpha(x)=c(x,a)+\alpha\int v_\alpha\,dq(\cdot\mid x,a)\}$ are nonempty; $\mathrm{Gr}(A_\alpha)$ is Borel; $A_\alpha(x)=A(x)$ if $v_\alpha(x)=+\infty$, and $A_\alpha(x)$ is compact if $v_\alpha(x)<+\infty$;
--   3. (v) there is a stationary discount optimal policy, and a stationary policy $\phi$ is discount optimal if and only if $\phi(x)\in A_\alpha(x)$ for all $x$;
--   4. (vi) if Assumption $(\mathrm{Wu})$ holds, the functions $v_{n,\alpha}$, $n\ge1$, and $v_\alpha$ are inf-compact on $\mathbb X$.
--
--   Parts (ii) and (iii) of the paper's theorem (finite-horizon equations and Markov policies) are not used by the goal and are not stated here.
--
--   **Formalization Note** The state and action spaces are types $\mathbb X$, $\mathbb A$ with a separable metrizable topology whose Borel $\sigma$-algebra is standard Borel; by the Lusin–Souslin theorem these are, up to homeomorphism, exactly the Borel subsets of Polish spaces of the paper. The model is the published `SchalAvg.AvgOpt.Model`: nonempty action sets $A(x)$ with measurable graph $\mathrm{Gr}(A)$, a Markov kernel $q$ on all of $\mathbb X\times\mathbb A$ (only its values on $\mathrm{Gr}(A)$ enter) and a cost $c$ with values in $[0,+\infty]$. The paper's cost is only bounded below; adding a constant to $c$ changes none of the statements (p. 595), so the nonnegative case is the general one. `HasSelector` is the paper's standing assumption (ii) of §2 (a measurable $\phi$ with $\phi(x)\in A(x)$). Optimal values are infima over all admissible (randomized, history-dependent) policies. The discount factor ranges over $[0,1)$, where $v_\alpha$ is defined. Discount optimality is the published `SchalAvg.AvgOpt.IsDiscOptimal` ($v^\phi_\alpha=v_\alpha$ everywhere).
-- source:
--   Feinberg, Kasyanov & Zadoianchuk, Average Cost Markov Decision Processes with Weakly Continuous Transition Probabilities, Math. Oper. Res. 37(4) 2012, pp. 598–599, Theorem 2 (i), (iv), (v), (vi)

import Mathlib
import Definitions.Def_FeinbergLiang_ACOE_MDP
import Definitions.Def_SchalAvg_AvgOpt_Model
import Definitions.Def_FKZAvg_WStar_Assumptions

open scoped ENNReal NNReal Topology
open MeasureTheory ProbabilityTheory Filter SchalAvg.AvgOpt

namespace FKZAvg.WStar

/-- Theorem 2 (i), (iv), (v), (vi) (pp. 598–599), for a discount factor `α ∈ [0, 1)`. -/
theorem theorem_2 {X A : Type*}
    [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X] [StandardBorelSpace X]
    [TopologicalSpace A] [TopologicalSpace.MetrizableSpace A] [SecondCountableTopology A]
    [MeasurableSpace A] [BorelSpace A] [StandardBorelSpace A]
    (M : Model X A) (hsel : HasSelector M)
    (hW : CondWStar M) (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α < 1) :
    -- (i)
    ((∀ n : ℕ, LowerSemicontinuous (vNOpt M n α)) ∧ LowerSemicontinuous (vβ M α) ∧
      ∀ x, Tendsto (fun n : ℕ => vNOpt M n α x) atTop (𝓝 (vβ M α x))) ∧
    -- (iv)
    ((∀ x, vβ M α x = ⨅ a ∈ M.Aset x, eta M (vβ M α) α x a) ∧
      (∀ x, (AAlpha M α x).Nonempty) ∧
      MeasurableSet {p : X × A | p.2 ∈ AAlpha M α p.1} ∧
      ∀ x, (vβ M α x = ⊤ → AAlpha M α x = M.Aset x) ∧
        (vβ M α x ≠ ⊤ → IsCompact (AAlpha M α x))) ∧
    -- (v)
    ((∃ φ : X → A, IsStationary M φ ∧ IsDiscOptimal M α φ) ∧
      ∀ φ : X → A, IsStationary M φ → (IsDiscOptimal M α φ ↔ ∀ x, φ x ∈ AAlpha M α x)) ∧
    -- (vi)
    (CondWu M → (∀ n : ℕ, 1 ≤ n → InfCompactOn (vNOpt M n α) Set.univ) ∧
      InfCompactOn (vβ M α) Set.univ) := by sorry

end FKZAvg.WStar
