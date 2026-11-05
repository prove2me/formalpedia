-- Prove2me | Theorems.Thm_BauerleRiederMDP_PDMDP_theorem_8_2_6
-- name    : BauerleRiederMDP.PDMDP.theorem_8_2_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:33:16.770278+00:00
-- url     : https://prove2.me/theorems/4dc0c2a9-fde2-4d38-9be4-3285b192387a
-- title:
--   Theorem 8.2.6 — the relaxed value is an upper semicontinuous fixed point of $T$ and an optimal relaxed policy exists
-- statement:
--   Let a Piecewise Deterministic Markov Decision Process be given, with state space $E\subset\mathbb R^d$, compact control space $U$, flow $\varphi$, jump kernel $Q$, jump rate $\lambda$ and reward rate $r$. Suppose that it has a continuous upper bounding function $b$ with $\alpha_b<1$ and that the continuity and compactness assumptions hold. Let $J^{rel}_\infty$ be the value function of the embedded discrete-time model with relaxed controls. Then:
--
--   1. $J^{rel}_\infty\in\mathbb M_{usc}$, that is, $J^{rel}_\infty\in\mathbb B_b^+$ and $J^{rel}_\infty$ is upper semicontinuous, and
--   $$
--   J^{rel}_\infty=TJ^{rel}_\infty.
--   $$
--   2. There exists an optimal relaxed Markov policy $\pi^*=(\pi^*_t)$ with $\pi^*_t=f(Z_n)(t-T_n)$ for $t\in(T_n,T_{n+1}]$, for a decision rule $f:E\to\mathcal R$.
--
--   This is the existence result of the chapter on the compact action space $\mathcal R$, on which Theorem 8.2.7 builds.
--
--   **Formalization Note** Optimality of $f$ means that the stationary policy $(f,f,\dots)$ attains $J^{rel}_\infty$ in the embedded model; a relaxed control has no physical process.
--
--   Differences from the source:
--   - encoding: U is a compact Borel subset of a Polish space → U is a nonempty compact metrizable space with its Borel σ-algebra; reason: a compact subset of a Polish space is exactly a compact metrizable space; every theorem here has U compact, and an empty U has no controls, so the book’s action sets are nonempty
--   - encoding: measurable f : E → A, and the book’s remark that it does not distinguish f from a jointly measurable map f̃ : ℝ₊ × E → U → a decision rule is that jointly measurable f̃; reason: this is the book’s own identification, p.245
--   - encoding: the drift μ with no printed measurability → μ is measurable; reason: standing convention of the book, needed for (8.7) to make sense
--   - encoding: value functions in [-∞, ∞) → EReal values, with integrals taken as the difference of the Lebesgue integrals of the positive and the negative part; reason: the bounding function makes the positive parts finite, so no ∞ - ∞ occurs
--   - encoding: measurable f : E → R, written f(s, x; du) → a Markov kernel from ℝ₊ × E to U; reason: the book’s notation f(s, x; du) of Remark 8.2.3 (ii); the jointly measurable version of a measurable map into R
--   - reading: α_b < 1 → α_b of the embedded model with relaxed controls, the supremum of ∫ b dQ′(·|x,α)/b(x) over x ∈ E and α ∈ R, with 0/0 = 0; reason: the book says b is a bounding function “with and without relaxed controls” and applies Theorem 7.2.1 to the relaxed model; the hypothesis is on α_b itself, not on its bound c_Q c_φ
--   - encoding: optimal relaxed Markov policy → the stationary policy attains J^{rel}_∞ in the embedded relaxed model; reason: for relaxed controls “there is no physical interpretation of the model” (p.250); the value J^{rel}_∞ is defined on the embedded model
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Theorem 8.2.6, p.253

import Mathlib
import Definitions.Def_BauerleRiederMDP_PDMDP_JumpModel_ContinuityCompactness
import Definitions.Def_BauerleRiederMDP_PDMDP_JumpModel_IsUpperBounding
import Definitions.Def_BauerleRiederMDP_PDMDP_JumpModel_relaxedStage
import Definitions.Def_BauerleRiederMDP_PDMDP_Model
import Definitions.Def_MDPFinance_PDMDP_Core

open MDPFinance.PDMDP (IBbPlus)

namespace BauerleRiederMDP.PDMDP

/-- Theorem 8.2.6 (Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), p.253, PDF 264). Suppose the Piecewise Deterministic Markov Decision
Process has a continuous upper bounding function `b` with `α_b < 1` and the continuity and
compactness assumptions are satisfied. Then
a) `J^{rel}_∞ ∈ IM_{usc}` and `J^{rel}_∞ = T J^{rel}_∞`;
b) there exists an optimal relaxed Markov policy `π*_t = f(Z_n)(t - T_n)`, `t ∈ (T_n, T_{n+1}]`, for
a decision rule `f : E → R`.

**Formalization Note** `α_b` is that of the embedded model with relaxed controls, the model the
proof applies Theorem 7.2.1 to. Optimality of the stationary policy `(f, f, …)` is
`J_∞(f, f, …) = J^{rel}_∞`: a relaxed control has no physical process (p.250, PDF 261), only the
embedded model. `U` is nonempty because the action set of the embedded model is. -/
theorem theorem_8_2_6 {d : ℕ} {E : Set (EuclideanSpace ℝ (Fin d))} {U : Type*}
    [TopologicalSpace U] [TopologicalSpace.MetrizableSpace U] [MeasurableSpace U] [BorelSpace U]
    [Nonempty U] (M : Model E U) (b : E → ℝ) (hb_cont : Continuous b)
    (hb : M.IsUpperBounding b) (hα : M.relaxedStage.alphaB b < 1)
    (hcc : M.ContinuityCompactness b) :
    (M.JinfRelaxed ∈ IBbPlus b ∧ UpperSemicontinuous M.JinfRelaxed ∧
        ∀ x, M.JinfRelaxed x = M.relaxedStage.T M.JinfRelaxed x) ∧
      ∃ f : RelaxedDecisionRule E U,
        ∀ x, M.relaxedStage.Jinf (fun _ => f.control) x = M.JinfRelaxed x := by sorry

end BauerleRiederMDP.PDMDP
