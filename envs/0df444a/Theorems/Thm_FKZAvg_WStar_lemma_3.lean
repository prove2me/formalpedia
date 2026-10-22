-- Prove2me | Theorems.Thm_FKZAvg_WStar_lemma_3
-- name    : FKZAvg.WStar.lemma_3
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:35:18.173171+00:00
-- url     : https://prove2.me/theorems/dde829fc-13bd-48d8-b55f-8abc662f04cc
-- title:
--   Lemma 3 — under (W*), u* of (15) is in L(𝕏), has a Borel minimizer f ∈ 𝔽, and A_*(x) of (17) has a Borel graph and compact values
-- statement:
--   Consider a Borel Markov decision process with action sets $A(x)$, one-step cost $c$ and transition probability $q$, satisfying Assumption $(\mathrm W^*)$. Let $u\in L(\mathbb X)$ (lower semicontinuous, bounded below, finite somewhere) and
--
--   $$u^*(x)=\inf_{a\in A(x)}\Big[c(x,a)+\int_{\mathbb X}u(y)\,q(dy\mid x,a)\Big],\qquad x\in\mathbb X.\tag{15}$$
--
--   Then:
--
--   1. $u^*\in L(\mathbb X)$;
--   2. there is a stationary policy $f$ (a Borel map with $f(x)\in A(x)$) with $u^*(x)=c(x,f(x))+\int u(y)\,q(dy\mid x,f(x))$ for all $x$ (16);
--   3. the infimum in (15) is attained, i.e. the sets $A_*(x)=\{a\in A(x): u^*(x)=c(x,a)+\int u(y)\,q(dy\mid x,a)\}$ (17) are nonempty;
--   4. the graph $\mathrm{Gr}(A_*)$ is a Borel subset of $\mathbb X\times\mathbb A$;
--   5. if $u^*(x)=+\infty$ then $A_*(x)=A(x)$, and if $u^*(x)<+\infty$ then $A_*(x)$ is compact.
--
--   This is the measurable-selection step used for the discounted optimality equation and for the selector in the average cost optimality inequality.
--
--   **Formalization Note** The state and action spaces are types $\mathbb X$, $\mathbb A$ with a separable metrizable topology whose Borel $\sigma$-algebra is standard Borel; by the Lusin–Souslin theorem these are, up to homeomorphism, exactly the Borel subsets of Polish spaces of the paper. The model is the published `SchalAvg.AvgOpt.Model`: nonempty action sets $A(x)$ with measurable graph $\mathrm{Gr}(A)$, a Markov kernel $q$ on all of $\mathbb X\times\mathbb A$ (only its values on $\mathrm{Gr}(A)$ enter) and a cost $c$ with values in $[0,+\infty]$. The paper's cost is only bounded below; adding a constant to $c$ changes none of the statements (p. 595), so the nonnegative case is the general one. `HasSelector` is the paper's standing assumption (ii) of §2 (a measurable $\phi$ with $\phi(x)\in A(x)$). Optimal values are infima over all admissible (randomized, history-dependent) policies. $u$ and $u^*$ are $[0,+\infty]$-valued (a bounded below $u$ shifts to this case), and $u\in L(\mathbb X)$ is `InL u`: lower semicontinuous with some $x$ where $u(x)\neq+\infty$. Conclusion 1 is stated as printed; see the variant `lemma_3_corrected` and finding F4.
-- source:
--   Feinberg, Kasyanov & Zadoianchuk, Average Cost Markov Decision Processes with Weakly Continuous Transition Probabilities, Math. Oper. Res. 37(4) 2012, p. 597, Lemma 3

import Mathlib
import Definitions.Def_FeinbergLiang_ACOE_MDP
import Definitions.Def_SchalAvg_AvgOpt_Model
import Definitions.Def_FKZAvg_WStar_Assumptions

open scoped ENNReal NNReal Topology
open MeasureTheory ProbabilityTheory Filter SchalAvg.AvgOpt

namespace FKZAvg.WStar

/-- Lemma 3 (p. 597), as printed. -/
theorem lemma_3 {X A : Type*}
    [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X] [StandardBorelSpace X]
    [TopologicalSpace A] [TopologicalSpace.MetrizableSpace A] [SecondCountableTopology A]
    [MeasurableSpace A] [BorelSpace A] [StandardBorelSpace A]
    (M : Model X A) (hsel : HasSelector M)
    (hW : CondWStar M) (u : X → ℝ≥0∞) (hu : InL u) :
    InL (uStar M u) ∧
    (∃ f : X → A, IsStationary M f ∧ ∀ x, uStar M u x = eta M u 1 x (f x)) ∧
    (∀ x, (AsubStar M u x).Nonempty) ∧
    MeasurableSet {p : X × A | p.2 ∈ AsubStar M u p.1} ∧
    ∀ x, (uStar M u x = ⊤ → AsubStar M u x = M.Aset x) ∧
      (uStar M u x ≠ ⊤ → IsCompact (AsubStar M u x)) := by sorry

end FKZAvg.WStar
