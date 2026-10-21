-- Prove2me | Theorems.Thm_FKZAvg_WStar_corollary_1
-- name    : FKZAvg.WStar.corollary_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:35:21.901436+00:00
-- url     : https://prove2.me/theorems/c2502adb-12fc-4ae1-8145-2c9ddef0838b
-- title:
--   Corollary 1 — under (B̲), u̲_{α_n}(x) ↑ u(x) = lim_{n→∞, y→x} u̲_{α_n}(y) for every α_n ↑ 1
-- statement:
--   Consider a Borel Markov decision process satisfying Assumption $(\underline{\mathrm B})$, with $u$ of (21) and $\underline u_\beta$ of (22) (see `FKZAvg.WStar.Assumptions`). For every sequence of discount factors $\alpha_n\in[0,1)$ with $\alpha_n\uparrow1$ and every $x\in\mathbb X$,
--
--   $$\underline u_{\alpha_n}(x)\uparrow u(x)=\lim_{n\to\infty,\,y\to x}\underline u_{\alpha_n}(y).$$
--
--   That is, $n\mapsto\underline u_{\alpha_n}(x)$ is nondecreasing and converges to $u(x)$, and $\underline u_{\alpha_n}(y)\to u(x)$ jointly as $n\to\infty$ and $y\to x$.
--
--   It is the bridge between the discounted relative values and the function $u$ in the proof of Lemma 7.
--
--   **Formalization Note** The state and action spaces are types $\mathbb X$, $\mathbb A$ with a separable metrizable topology whose Borel $\sigma$-algebra is standard Borel; by the Lusin–Souslin theorem these are, up to homeomorphism, exactly the Borel subsets of Polish spaces of the paper. The model is the published `SchalAvg.AvgOpt.Model`: nonempty action sets $A(x)$ with measurable graph $\mathrm{Gr}(A)$, a Markov kernel $q$ on all of $\mathbb X\times\mathbb A$ (only its values on $\mathrm{Gr}(A)$ enter) and a cost $c$ with values in $[0,+\infty]$. The paper's cost is only bounded below; adding a constant to $c$ changes none of the statements (p. 595), so the nonnegative case is the general one. `HasSelector` is the paper's standing assumption (ii) of §2 (a measurable $\phi$ with $\phi(x)\in A(x)$). Optimal values are infima over all admissible (randomized, history-dependent) policies. $\alpha_n\uparrow1$ is the published `FeinbergLiang.ACOE.IsDiscountSeq` ($\alpha_n\in[0,1)$, nondecreasing, $\alpha_n\to1$). The joint limit is along the product filter $\mathrm{atTop}\times\mathcal N(x)$, with $y=x$ allowed. The statement is as printed; see the variant `corollary_1_corrected` and finding F1, which shows the joint limit can fail to exist.
-- source:
--   Feinberg, Kasyanov & Zadoianchuk, Average Cost Markov Decision Processes with Weakly Continuous Transition Probabilities, Math. Oper. Res. 37(4) 2012, p. 601, Corollary 1

import Mathlib
import Definitions.Def_FeinbergLiang_ACOE_MDP
import Definitions.Def_SchalAvg_AvgOpt_Model
import Definitions.Def_FKZAvg_WStar_Assumptions

open scoped ENNReal NNReal Topology
open MeasureTheory ProbabilityTheory Filter SchalAvg.AvgOpt

namespace FKZAvg.WStar

/-- Corollary 1 (p. 601), as printed: `u̲_{α_n}(x) ↑ u(x) = lim_{n → ∞, y → x} u̲_{α_n}(y)`. -/
theorem corollary_1 {X A : Type*}
    [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X] [StandardBorelSpace X]
    [TopologicalSpace A] [TopologicalSpace.MetrizableSpace A] [SecondCountableTopology A]
    [MeasurableSpace A] [BorelSpace A] [StandardBorelSpace A]
    (M : Model X A) (hsel : HasSelector M) (hB : CondBLow M)
    (αs : ℕ → ℝ) (hαs : FeinbergLiang.ACOE.IsDiscountSeq αs) (x : X) :
    Monotone (fun n => uLow M (αs n) x) ∧
    Tendsto (fun n => uLow M (αs n) x) atTop (𝓝 (uAvg M x)) ∧
    Tendsto (fun p : ℕ × X => uLow M (αs p.1) p.2) (atTop ×ˢ 𝓝 x) (𝓝 (uAvg M x)) := by sorry

end FKZAvg.WStar
