-- Prove2me | Theorems.Thm_DRUQChance_Markov_sec5_feasible_iff
-- name    : DRUQChance.Markov.sec5_feasible_iff
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T18:48:59.013809+00:00
-- url     : https://prove2.me/theorems/beedf888-3474-47ac-a881-a4c29b1769df
-- title:
--   §5 feasibility claim with (17) at I = 1, p. 24 — the chance constraint holds iff (17) has a feasible point of value ≥ 1 − ε
-- statement:
--   Let $\mathcal P$ be a Markov ambiguity set: the set of probability distributions $\mathbb P$ of $(\tilde z,\tilde u) \in \mathbb R^P\times\mathbb R^Q$ with $\mathbb E_{\mathbb P}[A\tilde z + B\tilde u] = b$ and $\mathbb P[(\tilde z,\tilde u) \in \mathcal C_1] = 1$, where $\mathcal C_1 = \{(z,u) : C_1 z + D_1 u \preccurlyeq_{\mathcal K_1} d_1\}$ and $\mathcal K_1$ is a proper cone (closed, convex, pointed, with nonempty interior). Assume moreover that $\mathcal C_1$ is essentially strictly feasible and that the Slater condition (S) holds. Let $S \in \mathbb R^{J\times P}$ with rows $s_j^\top$, $t \in \mathbb R^J$ and $\epsilon \in (0,1)$.
--
--   Then the distributionally robust chance constraint
--   $$\inf_{\mathbb P \in \mathcal P}\ \mathbb P[S\tilde z \le t] \;\ge\; 1-\epsilon$$
--   holds if and only if the conic program (17) for $I = 1$ has a **feasible point** $(\gamma,\lambda,\kappa,\phi,\tau,\psi)$ with
--   $$b^\top\gamma + \underline p_1\lambda - \overline p_1\kappa \;\ge\; 1-\epsilon.$$
--
--   The paper states this in §5 for the unified uncertainty quantification problem $Q(\psi)$, $\psi \in \mathcal Q(x)$: a decision $x$ is feasible in the chance constrained program (2) iff some $\psi \in \mathcal Q(x)$ has $Q(\psi) \ge 1-\epsilon$. Here the claim is stated for problem (17) with $I = 1$ at one fixed decision: $S$ and $t$ stand for $S(x)$ and $t(x)$, and the requirement $x \in \mathcal X$, identical on both sides, is omitted. Beyond Theorem 3 it asserts that the value $1-\epsilon$ is reached by an actual feasible point, not only approached by a supremum.
--
--   **Formalization Note** $\mathbb R^n$ is `Fin n → ℝ`; the paper's single confidence set ($I = 1$) is the index `0 : Fin 1` of `AmbData nP nQ nK 0` from the published module `DRConvexOpt.Reform.Setting`, whose field `c 0` is the paper's $d_1$ and whose `plo 0`, `phi 0` are $\underline p_1$, $\overline p_1$. $\mathbb P[\cdot]$ is `μ.real`. The local `paperAmbiguitySet` retains the reused data and confidence sets, but requires integrability only of $A\tilde z+B\tilde u$, exactly the moment in (4); when $K=0$, this condition is void as the paper states on p. 6. The chance constraint is written as "$1-\epsilon \le \mathbb P[S\tilde z \le t]$ for every $\mathbb P \in \mathcal P$", which equals the infimum form in the extended reals and avoids `sInf ∅ = 0`. The paper's $\epsilon \in (0,1)$ (p. 2), proper $\mathcal K_1$, essential strict feasibility and (S) are explicit hypotheses.
-- source:
--   Hanasusanto, Roitch, Kuhn & Wiesemann, A distributionally robust perspective on uncertainty quantification and chance constrained programming, Math. Program. 151(1) (2015); authors' accepted manuscript, p. 24, §5 (sentence before (30)), applied to problem (17) of Theorem 3 at I = 1 (pp. 11–12)

import Mathlib
import Definitions.Def_DRConvexOpt_Reform_Setting
import Definitions.Def_DRUQChance_Markov_Basic

namespace DRUQChance.Markov

open MeasureTheory Matrix DRConvexOpt.Reform

/-- The §5 feasibility claim (p. 24) with problem (17) at `I = 1`: for a Markov ambiguity set
with proper cone `K₁`, essentially strictly feasible `C₁` and (S), and `ε ∈ (0, 1)`, the
chance constraint `inf_ℙ ℙ[S z̃ ≤ t] ≥ 1 − ε` holds iff some feasible point of (17) has
objective value at least `1 − ε`. -/
theorem sec5_feasible_iff {nP nQ nK nJ : ℕ} (amb : AmbData nP nQ nK 0) (hM : IsMarkov amb)
    (hK : IsProperCone (amb.K 0))
    (hE : EssStrictFeas (amb.C 0) (amb.D 0) (amb.c 0) (amb.K 0)) (hS : SlaterI1 amb)
    (S : Matrix (Fin nJ) (Fin nP) ℝ) (t : Fin nJ → ℝ) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) :
    (∀ μ ∈ paperAmbiguitySet amb, 1 - ε ≤ μ.real {ω | S *ᵥ ω.1 ≤ t}) ↔
      ∃ (γ : Fin nK → ℝ) (lam kap : ℝ) (φ : Fin (amb.L 0) → ℝ) (τ : Fin nJ → ℝ)
        (ψ : Fin nJ → Fin (amb.L 0) → ℝ),
        UQFeasible amb S t γ lam kap φ τ ψ ∧ 1 - ε ≤ uqObjective amb γ lam kap := by sorry

end DRUQChance.Markov
