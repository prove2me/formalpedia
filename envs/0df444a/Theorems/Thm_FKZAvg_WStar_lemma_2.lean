-- Prove2me | Theorems.Thm_FKZAvg_WStar_lemma_2
-- name    : FKZAvg.WStar.lemma_2
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:35:25.722416+00:00
-- url     : https://prove2.me/theorems/3a75c5df-d896-41db-be09-52a63fa38e05
-- title:
--   Lemma 2 — under (W*(ii)) c(x,·) is inf-compact on A(x); under (W*(ii, iii)) so is η^α_u(x,·) for u ∈ L(𝕏), α ≥ 0
-- statement:
--   Consider a Borel Markov decision process with action sets $A(x)$, one-step cost $c$ and transition probability $q$. For a lower semicontinuous, bounded below $u:\mathbb X\to\mathbb R\cup\{+\infty\}$ with $\{u<+\infty\}\neq\emptyset$ (the class $L(\mathbb X)$) and $\alpha\ge0$ put $\eta^\alpha_u(x,a)=c(x,a)+\alpha\int_{\mathbb X}u(y)\,q(dy\mid x,a)$. For every $x\in\mathbb X$:
--
--   1. under Assumption $(\mathrm W^*(\mathrm{ii}))$ alone, the function $c(x,\cdot)$ is inf-compact on $A(x)$;
--   2. under Assumptions $(\mathrm W^*(\mathrm{ii},\mathrm{iii}))$ alone, for every $u\in L(\mathbb X)$ and $\alpha\ge0$, the function $\eta^\alpha_u(x,\cdot)$ is inf-compact on $A(x)$.
--
--   Here inf-compact on $A(x)$ means that every level set $\{a\in A(x): f(a)\le\lambda\}$, $\lambda\in\mathbb R$, is compact. The lemma is the compactness input for the attained minima of Lemma 3 and Theorem 2.
--
--   **Formalization Note** The state and action spaces are types $\mathbb X$, $\mathbb A$ with a separable metrizable topology whose Borel $\sigma$-algebra is standard Borel; by the Lusin–Souslin theorem these are, up to homeomorphism, exactly the Borel subsets of Polish spaces of the paper. The model is the published `SchalAvg.AvgOpt.Model`: nonempty action sets $A(x)$ with measurable graph $\mathrm{Gr}(A)$, a Markov kernel $q$ on all of $\mathbb X\times\mathbb A$ (only its values on $\mathrm{Gr}(A)$ enter) and a cost $c$ with values in $[0,+\infty]$. The paper's cost is only bounded below; adding a constant to $c$ changes none of the statements (p. 595), so the nonnegative case is the general one. `HasSelector` is the paper's standing assumption (ii) of §2 (a measurable $\phi$ with $\phi(x)\in A(x)$). Optimal values are infima over all admissible (randomized, history-dependent) policies. The statement is the paper's, with only (W*(ii)), resp. (W*(ii, iii)), assumed; see the variant `lemma_2_corrected` and finding F3.
-- source:
--   Feinberg, Kasyanov & Zadoianchuk, Average Cost Markov Decision Processes with Weakly Continuous Transition Probabilities, Math. Oper. Res. 37(4) 2012, p. 596, Lemma 2

import Mathlib
import Definitions.Def_FeinbergLiang_ACOE_MDP
import Definitions.Def_SchalAvg_AvgOpt_Model
import Definitions.Def_FKZAvg_WStar_Assumptions

open scoped ENNReal NNReal Topology
open MeasureTheory ProbabilityTheory Filter SchalAvg.AvgOpt

namespace FKZAvg.WStar

/-- Lemma 2 (p. 596), as printed: (a) under (W*(ii)) only, (b) under (W*(ii, iii)) only. -/
theorem lemma_2 {X A : Type*}
    [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X] [StandardBorelSpace X]
    [TopologicalSpace A] [TopologicalSpace.MetrizableSpace A] [SecondCountableTopology A]
    [MeasurableSpace A] [BorelSpace A] [StandardBorelSpace A]
    (M : Model X A) (hsel : HasSelector M) (x : X) :
    (CondWStar_ii M → InfCompactOn (fun a => M.toMDP.cost x a) (M.Aset x)) ∧
    (CondWStar_ii M → CondWStar_iii M →
      ∀ u : X → ℝ≥0∞, InL u → ∀ α : ℝ, 0 ≤ α →
        InfCompactOn (fun a => eta M u α x a) (M.Aset x)) := by sorry

end FKZAvg.WStar
