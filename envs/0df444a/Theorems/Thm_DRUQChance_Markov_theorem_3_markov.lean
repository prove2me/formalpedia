-- Prove2me | Theorems.Thm_DRUQChance_Markov_theorem_3_markov
-- name    : DRUQChance.Markov.theorem_3_markov
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T18:48:43.281609+00:00
-- url     : https://prove2.me/theorems/d987619c-4db4-4239-8ce0-e3dd11510a9b
-- title:
--   Theorem 3 (case I = 1), pp. 11–12 — over a Markov ambiguity set the worst-case probability equals the optimal value of (17)
-- statement:
--   Let $\mathcal P$ be a Markov ambiguity set: the set of probability distributions $\mathbb P$ of $(\tilde z,\tilde u) \in \mathbb R^P\times\mathbb R^Q$ with $\mathbb E_{\mathbb P}[A\tilde z + B\tilde u] = b$ and $\mathbb P[(\tilde z,\tilde u) \in \mathcal C_1] = 1$, where $\mathcal C_1 = \{(z,u) : C_1 z + D_1 u \preccurlyeq_{\mathcal K_1} d_1\}$ and $\mathcal K_1$ is a proper cone (closed, convex, pointed, with nonempty interior). Assume moreover that $\mathcal C_1$ is essentially strictly feasible and that the Slater condition (S) holds, i.e. $b$ lies in the interior of $\{Az + Bu : (z,u) \in \mathcal C_1\}$.
--
--   Let $S \in \mathbb R^{J\times P}$ have rows $s_j^\top$ and let $t \in \mathbb R^J$. Then the worst-case probability
--   $$\inf_{\mathbb P \in \mathcal P}\ \mathbb P[S\tilde z \le t]$$
--   coincides with the optimal value of the conic program (17) for $I = 1$:
--   $$\begin{aligned} \sup\ & b^\top\gamma + \underline p_1\lambda - \overline p_1\kappa\\ \text{s.t. }& \gamma \in \mathbb R^K,\ \lambda,\kappa \ge 0,\ \phi \in \mathcal K_1^\star,\ \tau_j \ge 0,\ \psi_j \in \mathcal K_1^\star\ (j \in \mathcal L)\\ & \lambda - \kappa + d_1^\top\phi \le 1,\quad A^\top\gamma = C_1^\top\phi,\quad B^\top\gamma = D_1^\top\phi\\ & \lambda - \kappa + d_1^\top\psi_j - \tau_j t_j \le 0,\quad A^\top\gamma + \tau_j s_j = C_1^\top\psi_j,\quad B^\top\gamma = D_1^\top\psi_j \quad (j \in \mathcal L), \end{aligned}$$
--   where $\mathcal L = \{j : \exists (z,u) \in \mathcal C_1,\ s_j^\top z > t_j\}$.
--
--   This is Theorem 3 of the paper in the case of a single confidence set (a Markov ambiguity set). It turns the infinite-dimensional uncertainty quantification problem (1) into a finite conic program. The general nested case ($I > 1$) is not stated, because the paper does not make the Slater condition (S) explicit for $I > 1$.
--
--   **Formalization Note** $\mathbb R^n$ is `Fin n → ℝ`; the paper's single confidence set ($I = 1$) is the index `0 : Fin 1` of `AmbData nP nQ nK 0` from the published module `DRConvexOpt.Reform.Setting`, whose field `c 0` is the paper's $d_1$ and whose `plo 0`, `phi 0` are $\underline p_1$, $\overline p_1$. $\mathbb P[\cdot]$ is `μ.real`. The local `paperAmbiguitySet` retains the reused data and confidence sets, but requires integrability only of $A\tilde z+B\tilde u$, exactly the moment in (4); when $K=0$, this condition is void as the paper states on p. 6. "Coincides with the optimal value" is stated as: there is one real number $v$ that is the greatest lower bound of the probabilities $\{\mathbb P[S\tilde z \le t] : \mathbb P \in \mathcal P\}$ and the least upper bound of the objective values of feasible points of (17) (`IsGLB`/`IsLUB`), avoiding Lean's junk values of `sInf`/`sSup`. The paper's standing assumptions (proper $\mathcal K_1$, essential strict feasibility, p. 6) and (S) at $I = 1$ (p. 11) are explicit hypotheses; essential strict feasibility is read as in `DRUQChance.Markov.Basic`.
-- source:
--   Hanasusanto, Roitch, Kuhn & Wiesemann, A distributionally robust perspective on uncertainty quantification and chance constrained programming, Math. Program. 151(1) (2015); authors' accepted manuscript, pp. 11–12, Theorem 3 (case I = 1), (17); (S) for I = 1 on p. 11

import Mathlib
import Definitions.Def_DRConvexOpt_Reform_Setting
import Definitions.Def_DRUQChance_Markov_Basic

namespace DRUQChance.Markov

open MeasureTheory Matrix DRConvexOpt.Reform

/-- Theorem 3 at `I = 1` (pp. 11–12): for a Markov ambiguity set with proper cone `K₁`,
essentially strictly feasible `C₁` and the Slater condition (S), the worst-case probability
`inf_ℙ ℙ[S z̃ ≤ t]` and the optimal value of (17) are the same real number `v`. -/
theorem theorem_3_markov {nP nQ nK nJ : ℕ} (amb : AmbData nP nQ nK 0) (hM : IsMarkov amb)
    (hK : IsProperCone (amb.K 0))
    (hE : EssStrictFeas (amb.C 0) (amb.D 0) (amb.c 0) (amb.K 0)) (hS : SlaterI1 amb)
    (S : Matrix (Fin nJ) (Fin nP) ℝ) (t : Fin nJ → ℝ) :
    ∃ v : ℝ,
      IsGLB {p : ℝ | ∃ μ ∈ paperAmbiguitySet amb, p = μ.real {ω | S *ᵥ ω.1 ≤ t}} v ∧
      IsLUB {o : ℝ | ∃ (γ : Fin nK → ℝ) (lam kap : ℝ) (φ : Fin (amb.L 0) → ℝ)
          (τ : Fin nJ → ℝ) (ψ : Fin nJ → Fin (amb.L 0) → ℝ),
          UQFeasible amb S t γ lam kap φ τ ψ ∧ o = uqObjective amb γ lam kap} v := by sorry

end DRUQChance.Markov
