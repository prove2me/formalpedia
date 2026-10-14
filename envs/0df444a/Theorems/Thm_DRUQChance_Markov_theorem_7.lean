-- Prove2me | Theorems.Thm_DRUQChance_Markov_theorem_7
-- name    : DRUQChance.Markov.theorem_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T18:48:50.136978+00:00
-- url     : https://prove2.me/theorems/4eafb1ef-c3a9-4f84-8f38-a412647fda32
-- title:
--   Theorem 7, p. 18 — an individual chance constraint over a Markov ambiguity set holds iff the linear conic system (26) is solvable
-- statement:
--   Let $\mathcal P$ be a Markov ambiguity set: the set of probability distributions $\mathbb P$ of $(\tilde z,\tilde u) \in \mathbb R^P\times\mathbb R^Q$ with $\mathbb E_{\mathbb P}[A\tilde z + B\tilde u] = b$ and $\mathbb P[(\tilde z,\tilde u) \in \mathcal C_1] = 1$, where $\mathcal C_1 = \{(z,u) : C_1 z + D_1 u \preccurlyeq_{\mathcal K_1} d_1\}$ and $\mathcal K_1$ is a proper cone (closed, convex, pointed, with nonempty interior). Assume moreover that $\mathcal C_1$ is essentially strictly feasible (it contains a point satisfying all non-polyhedral constraints strictly) and that the Slater condition (S) holds: $b$ lies in the interior of $\{Az + Bu : (z,u) \in \mathcal C_1\}$. Let $s \in \mathbb R^P$, $t \in \mathbb R$ and $\epsilon \in (0,1)$.
--
--   Then the individual distributionally robust chance constraint
--   $$\inf_{\mathbb P \in \mathcal P}\ \mathbb P[s^\top\tilde z \le t] \;\ge\; 1-\epsilon$$
--   holds if and only if there are $\beta \in \mathbb R$, $\gamma \in \mathbb R^K$, $\phi,\psi \in \mathcal K_1^\star$ and $\tau \in \mathbb R_+$ such that
--   $$\begin{aligned} &\beta + b^\top\gamma \ge (1-\epsilon)\tau, && \beta + d_1^\top\phi \le \tau, && \beta + d_1^\top\psi \le t,\\ &A^\top\gamma = C_1^\top\phi, && B^\top\gamma = D_1^\top\phi, &&\\ &A^\top\gamma + s = C_1^\top\psi, && B^\top\gamma = D_1^\top\psi. && \end{aligned} \qquad (26)$$
--
--   This is Theorem 7 of the paper. Since $s(x)$ and $t(x)$ are affine in the design decision $x$, (26) turns the chance constrained program (2) with $J = 1$ over a Markov ambiguity set into a problem with finitely many conic constraints; Theorem 8 of the paper shows that the restriction to Markov sets cannot be dropped. Here $s$ and $t$ stand for $s(x)$ and $t(x)$ at one fixed $x$; the outer program (2) and $\mathcal X$ are not formalized.
--
--   **Formalization Note** $\mathbb R^n$ is `Fin n → ℝ`; the paper's single confidence set ($I = 1$) is the index `0 : Fin 1` of `AmbData nP nQ nK 0` from the published module `DRConvexOpt.Reform.Setting`, whose field `c 0` is the paper's $d_1$ and whose `plo 0`, `phi 0` are $\underline p_1$, $\overline p_1$. $\mathbb P[\cdot]$ is `μ.real`. The local `paperAmbiguitySet` retains the reused data and confidence sets, but requires integrability only of $A\tilde z+B\tilde u$, exactly the moment in (4); when $K=0$, this condition is void as the paper states on p. 6. The chance constraint is written as "$1-\epsilon \le \mathbb P[s^\top\tilde z \le t]$ for every $\mathbb P \in \mathcal P$", which equals the infimum form in the extended reals and avoids `sInf ∅ = 0`. The paper leaves implicit that $\epsilon \in (0,1)$ (p. 2), that $\mathcal K_1$ is proper and $\mathcal C_1$ essentially strictly feasible (standing assumptions, p. 6); all are explicit hypotheses here, and essential strict feasibility is read as in `DRUQChance.Markov.Basic`.
-- source:
--   Hanasusanto, Roitch, Kuhn & Wiesemann, A distributionally robust perspective on uncertainty quantification and chance constrained programming, Math. Program. 151(1) (2015); authors' accepted manuscript, p. 18, Theorem 7 and (26)

import Mathlib
import Definitions.Def_DRConvexOpt_Reform_Setting
import Definitions.Def_DRUQChance_Markov_Basic

namespace DRUQChance.Markov

open MeasureTheory Matrix DRConvexOpt.Reform

/-- Theorem 7 (p. 18): for a Markov ambiguity set with proper cone `K₁`, essentially strictly
feasible `C₁` and the Slater condition (S), and `ε ∈ (0, 1)`, the individual chance constraint
`inf_ℙ ℙ[sᵀ z̃ ≤ t] ≥ 1 − ε` holds iff the linear conic system (26) is solvable. -/
theorem theorem_7 {nP nQ nK : ℕ} (amb : AmbData nP nQ nK 0) (hM : IsMarkov amb)
    (hK : IsProperCone (amb.K 0))
    (hE : EssStrictFeas (amb.C 0) (amb.D 0) (amb.c 0) (amb.K 0)) (hS : SlaterI1 amb)
    (s : Fin nP → ℝ) (t ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) :
    (∀ μ ∈ paperAmbiguitySet amb, 1 - ε ≤ μ.real {ω | s ⬝ᵥ ω.1 ≤ t}) ↔
      ∃ (β : ℝ) (γ : Fin nK → ℝ) (φ ψ : Fin (amb.L 0) → ℝ) (τ : ℝ),
        System26 amb s t ε β γ φ ψ τ := by sorry

end DRUQChance.Markov
