-- Prove2me | Theorems.Thm_FKZAvg_WStar_lemma_6
-- name    : FKZAvg.WStar.lemma_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:35:26.996676+00:00
-- url     : https://prove2.me/theorems/bbfd4eef-28ea-49c0-b158-c3b7b0ac2d90
-- title:
--   Lemma 6 — under (B̲), u of (21) and u̲_α of (22) are finite and lower semicontinuous; with (W*) so are u_α; with (Wu) all are inf-compact
-- statement:
--   Consider a Borel Markov decision process; let $v_\alpha$ be the optimal $\alpha$-discounted cost, $m_\alpha=\inf_x v_\alpha(x)$, $u_\alpha=v_\alpha-m_\alpha$, $U_\beta(x)=\inf_{\alpha\in[\beta,1)}u_\alpha(x)$, $\underline u_\beta(x)=\liminf_{y\to x}U_\beta(y)$ (22), and $u(x)=\liminf_{\alpha\uparrow1,\,y\to x}u_\alpha(y)$ (21). Under Assumption $(\underline{\mathrm B})$:
--
--   1. the functions $u$ and $\underline u_\alpha$, $\alpha\in[0,1)$, take finite nonnegative values and are lower semicontinuous on $\mathbb X$;
--   2. if in addition Assumption $(\mathrm W^*)$ holds, the functions $u_\alpha$, $\alpha\in[0,1)$, take finite nonnegative values and are lower semicontinuous;
--   3. if in addition Assumption $(\mathrm{Wu})$ holds, the functions $u$, $u_\alpha$, $\underline u_\alpha$, $\alpha\in[0,1)$, take finite nonnegative values and are inf-compact on $\mathbb X$.
--
--   This gives part (a) and part (e) of Theorem 3.
--
--   **Formalization Note** The state and action spaces are types $\mathbb X$, $\mathbb A$ with a separable metrizable topology whose Borel $\sigma$-algebra is standard Borel; by the Lusin–Souslin theorem these are, up to homeomorphism, exactly the Borel subsets of Polish spaces of the paper. The model is the published `SchalAvg.AvgOpt.Model`: nonempty action sets $A(x)$ with measurable graph $\mathrm{Gr}(A)$, a Markov kernel $q$ on all of $\mathbb X\times\mathbb A$ (only its values on $\mathrm{Gr}(A)$ enter) and a cost $c$ with values in $[0,+\infty]$. The paper's cost is only bounded below; adding a constant to $c$ changes none of the statements (p. 595), so the nonnegative case is the general one. `HasSelector` is the paper's standing assumption (ii) of §2 (a measurable $\phi$ with $\phi(x)\in A(x)$). Optimal values are infima over all admissible (randomized, history-dependent) policies. The finiteness \"$:\mathbb X\to\mathbb R_+$\" of each function is stated as $f(x)\neq+\infty$ for every $x$, in each of the three clauses where the paper writes it. $u_\alpha$ is the published `wβ` ($v_\alpha-m_\alpha$ in $[0,+\infty]$, truncated at $0$; $m_\alpha<\infty$ under (G)).
-- source:
--   Feinberg, Kasyanov & Zadoianchuk, Average Cost Markov Decision Processes with Weakly Continuous Transition Probabilities, Math. Oper. Res. 37(4) 2012, p. 600, Lemma 6

import Mathlib
import Definitions.Def_FeinbergLiang_ACOE_MDP
import Definitions.Def_SchalAvg_AvgOpt_Model
import Definitions.Def_FKZAvg_WStar_Assumptions

open scoped ENNReal NNReal Topology
open MeasureTheory ProbabilityTheory Filter SchalAvg.AvgOpt

namespace FKZAvg.WStar

/-- Lemma 6 (p. 600). `uLow M α` is the paper's `u̲_α` of (22); `wβ M α` is `u_α`. -/
theorem lemma_6 {X A : Type*}
    [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X] [StandardBorelSpace X]
    [TopologicalSpace A] [TopologicalSpace.MetrizableSpace A] [SecondCountableTopology A]
    [MeasurableSpace A] [BorelSpace A] [StandardBorelSpace A]
    (M : Model X A) (hsel : HasSelector M) (hB : CondBLow M) :
    (LowerSemicontinuous (uAvg M) ∧ (∀ x, uAvg M x ≠ ⊤) ∧
      ∀ α ∈ Set.Ico (0 : ℝ) 1, LowerSemicontinuous (uLow M α) ∧ ∀ x, uLow M α x ≠ ⊤) ∧
    (CondWStar M → ∀ α ∈ Set.Ico (0 : ℝ) 1,
      LowerSemicontinuous (wβ M α) ∧ ∀ x, wβ M α x ≠ ⊤) ∧
    (CondWu M →
      (InfCompactOn (uAvg M) Set.univ ∧ ∀ x, uAvg M x ≠ ⊤) ∧
      ∀ α ∈ Set.Ico (0 : ℝ) 1,
        (InfCompactOn (wβ M α) Set.univ ∧ ∀ x, wβ M α x ≠ ⊤) ∧
        (InfCompactOn (uLow M α) Set.univ ∧ ∀ x, uLow M α x ≠ ⊤)) := by sorry

end FKZAvg.WStar
