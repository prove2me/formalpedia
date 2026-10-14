-- Prove2me | Theorems.Thm_DRUQChance_Markov_theorem_7_if
-- name    : DRUQChance.Markov.theorem_7_if
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T18:48:50.857412+00:00
-- url     : https://prove2.me/theorems/1db32837-a6c3-4bd5-9328-9cf415a317ef
-- title:
--   Theorem 7, sufficiency, p. 18 — a solution of (26) certifies the individual chance constraint over a Markov ambiguity set
-- statement:
--   Let $\mathcal P$ be a Markov ambiguity set: the set of probability distributions $\mathbb P$ of $(\tilde z,\tilde u) \in \mathbb R^P\times\mathbb R^Q$ with $\mathbb E_{\mathbb P}[A\tilde z + B\tilde u] = b$ and $\mathbb P[(\tilde z,\tilde u) \in \mathcal C_1] = 1$, where $\mathcal C_1 = \{(z,u) : C_1 z + D_1 u \preccurlyeq_{\mathcal K_1} d_1\}$ and $\mathcal K_1$ is a proper cone (closed, convex, pointed, with nonempty interior). Let $s \in \mathbb R^P$, $t \in \mathbb R$ and $\epsilon \in (0,1)$. If there are $\beta \in \mathbb R$, $\gamma \in \mathbb R^K$, $\phi,\psi \in \mathcal K_1^\star$ and $\tau \ge 0$ such that
--   $$\begin{aligned} &\beta + b^\top\gamma \ge (1-\epsilon)\tau, && \beta + d_1^\top\phi \le \tau, && \beta + d_1^\top\psi \le t,\\ &A^\top\gamma = C_1^\top\phi, && B^\top\gamma = D_1^\top\phi, &&\\ &A^\top\gamma + s = C_1^\top\psi, && B^\top\gamma = D_1^\top\psi, && \end{aligned} \qquad (26)$$
--   then
--   $$\mathbb P[s^\top\tilde z \le t] \;\ge\; 1-\epsilon \quad\text{for every } \mathbb P \in \mathcal P.$$
--
--   This is the "if" direction of Theorem 7 of the paper: the linear conic system (26) is a sufficient certificate for the individual chance constraint. Here $s$ and $t$ stand for $s(x)$ and $t(x)$ at one fixed design decision $x$; the outer program (2) and its feasible set $\mathcal X$ are not formalized. The case $\tau = 0$ is allowed, as in the paper. The statement does not assume (S) or essential strict feasibility of $\mathcal C_1$, which this direction does not need; this only strengthens it.
--
--   **Formalization Note** $\mathbb R^n$ is `Fin n → ℝ`; the paper's single confidence set ($I = 1$) is the index `0 : Fin 1` of `AmbData nP nQ nK 0` from the published module `DRConvexOpt.Reform.Setting`, whose field `c 0` is the paper's $d_1$ and whose `plo 0`, `phi 0` are $\underline p_1$, $\overline p_1$. $\mathbb P[\cdot]$ is `μ.real`. The local `paperAmbiguitySet` retains the reused data and confidence sets, but requires integrability only of $A\tilde z+B\tilde u$, exactly the moment in (4); when $K=0$, this condition is void as the paper states on p. 6. The chance constraint $\inf_{\mathbb P \in \mathcal P}\mathbb P[s^\top\tilde z \le t] \ge 1-\epsilon$ is written as a bound for every $\mathbb P \in \mathcal P$. The paper's $\epsilon \in (0,1)$ (p. 2) and proper $\mathcal K_1$ (p. 6) are explicit hypotheses.
-- source:
--   Hanasusanto, Roitch, Kuhn & Wiesemann, A distributionally robust perspective on uncertainty quantification and chance constrained programming, Math. Program. 151(1) (2015); authors' accepted manuscript, p. 18, Theorem 7 (sufficiency direction) and (26)

import Mathlib
import Definitions.Def_DRConvexOpt_Reform_Setting
import Definitions.Def_DRUQChance_Markov_Basic

namespace DRUQChance.Markov

open MeasureTheory Matrix DRConvexOpt.Reform

/-- Theorem 7, sufficiency (p. 18): for a Markov ambiguity set with proper cone `K₁` and
`ε ∈ (0, 1)`, any solution of (26) certifies the individual chance constraint
`inf_ℙ ℙ[sᵀ z̃ ≤ t] ≥ 1 − ε`. -/
theorem theorem_7_if {nP nQ nK : ℕ} (amb : AmbData nP nQ nK 0) (hM : IsMarkov amb)
    (hK : IsProperCone (amb.K 0)) (s : Fin nP → ℝ) (t ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (β : ℝ) (γ : Fin nK → ℝ) (φ ψ : Fin (amb.L 0) → ℝ) (τ : ℝ)
    (h26 : System26 amb s t ε β γ φ ψ τ) :
    ∀ μ ∈ paperAmbiguitySet amb, 1 - ε ≤ μ.real {ω | s ⬝ᵥ ω.1 ≤ t} := by sorry

end DRUQChance.Markov
