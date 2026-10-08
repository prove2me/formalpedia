-- Prove2me | Theorems.Thm_ClosedLoopMFG_MarkovNash_eq_4_6_4_7
-- name    : ClosedLoopMFG.MarkovNash.eq_4_6_4_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T03:32:10.532993+00:00
-- url     : https://prove2.me/theorems/2317d63a-4265-4160-99e7-a556c973ad8b
-- title:
--   (4.6)–(4.7) — a Markovian selection that matches the conditional drift and dominates the conditional reward
-- statement:
--   Assume Assumptions A and B. Fix a player $i$, Markovian controls $\alpha^j$ for the players $j\ne i$, and an admissible closed-loop control $\beta$ for player $i$. Let $\boldsymbol Y=(Y^1,\dots,Y^n)$ be a solution of the $n$-player state system in which player $i$ uses $\beta$ and every $j\ne i$ uses $\alpha^j$, and let $\nu^n_t=\frac1n\sum_{k=1}^n\delta_{Y^k_t}$. Then there is a Borel function $\widetilde\beta:[0,T]\times(\mathbb R^d)^n\to A$ such that, for each $t\in[0,T]$,
--   $$b(t,Y^i_t,\nu^n_t,\widetilde\beta(t,\boldsymbol Y_t))=\mathbb E\big[b(t,Y^i_t,\nu^n_t,\beta(t,\boldsymbol Y))\,\big|\,\boldsymbol Y_t\big]\quad\text{a.s.},\tag{4.6}$$
--   $$f(t,Y^i_t,\nu^n_t,\widetilde\beta(t,\boldsymbol Y_t))\ge\mathbb E\big[f(t,Y^i_t,\nu^n_t,\beta(t,\boldsymbol Y))\,\big|\,\boldsymbol Y_t\big]\quad\text{a.s.}\tag{4.7}$$
--
--   The paper justifies this by noting that the conditional expectation lies in the convex set $K(t,Y^i_t,\nu^n_t)$ of Assumption B and applying a measurable selection theorem. The selection $\widetilde\beta$ is the Markovian deviation that does at least as well as $\beta$.
--
--   **Formalization Note** The paper states this for player 1 ("the argument for other players $i\ne1$ is identical"); it is stated here for an arbitrary player $i$. The paper prints the membership display as $\mathbb E[b(t,Y^1_t,\nu^n_t,\beta(t,\boldsymbol Y))\mid\boldsymbol Y_t]\in K(t,Y^1_t,\nu^n_t)$, without the $f$-component; the statement here is (4.6)–(4.7) as printed, i.e. the existence of $\widetilde\beta$. $\mathbb E[\,\cdot\mid\boldsymbol Y_t]$ is the conditional expectation (vector-valued for $b$) with respect to $\sigma(\boldsymbol Y_t)$, and "for each $t$" means every $t\in[0,T]$. $\boldsymbol Y$ is any weak solution in the sense of the `Game` definition; the controls of the players $j\ne i$ are lifted by $\alpha^j(t,\boldsymbol x)=\tilde\alpha^j(t,\boldsymbol x_t)$.
-- source:
--   Lacker, On the convergence of closed-loop Nash equilibria to the mean field game limit, arXiv:1808.02745v1, p. 21, proof of Proposition 2.2 (Section 4.3), (4.6)–(4.7)

import Mathlib
import Definitions.Def_ClosedLoopMFG_MarkovNash_Model
import Definitions.Def_ClosedLoopMFG_MarkovNash_Game

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace ClosedLoopMFG.MarkovNash

/-- Lacker, arXiv:1808.02745v1, proof of Proposition 2.2 (§4.3, p. 21), (4.6)–(4.7): the measurable
selection. Let player `i` use an admissible closed-loop control `β` and every other player `j` a
Markovian control `α̃^j`, and let `Y` be a solution of the resulting `n`-player state system, with
empirical measure `ν^n_t`. Under Assumptions A and B there is a Borel `A`-valued
`β̃ : [0, T] × (ℝ^d)^n → A` such that, for each `t ∈ [0, T]`, almost surely,
`b(t, Y^i_t, ν^n_t, β̃(t, Y_t)) = E[b(t, Y^i_t, ν^n_t, β(t, Y)) | Y_t]` (4.6) and
`f(t, Y^i_t, ν^n_t, β̃(t, Y_t)) ≥ E[f(t, Y^i_t, ν^n_t, β(t, Y)) | Y_t]` (4.7). -/
theorem eq_4_6_4_7 {n d : ℕ} [NeZero n] {T : ℝ≥0} (hT : 0 < T)
    {EA : Type*} [NormedAddCommGroup EA] [NormedSpace ℝ EA] [MeasurableSpace EA] [BorelSpace EA]
    (A : Set EA) (lam : PR d) (b : ℝ → E d → PR d → EA → E d)
    (f : ℝ → E d → PR d → EA → ℝ) (g : E d → PR d → ℝ)
    (hA : AssumptionA T A b f g) (hB : AssumptionB T A b f)
    (α : Fin n → ℝ → (Fin n → E d) → EA) (i : Fin n)
    (hα : ∀ j, j ≠ i → IsMarkovControl (T := T) A (α j))
    (β : ℝ → (Fin n → Path d T) → EA) (hβ : IsAdmissible A β)
    (S : NSol n d T lam (drift b (Function.update (fun j => liftM (α j)) i β))) :
    ∃ βt : ℝ → (Fin n → E d) → EA, IsMarkovControl (T := T) A βt ∧
      ∀ t ∈ Set.Icc (0 : ℝ) T,
        ((fun ω => b t (snap (S.X ω) t i) (empirical (snap (S.X ω) t))
            (βt t (snap (S.X ω) t)))
          =ᵐ[S.P] S.P[fun ω => b t (snap (S.X ω) t i) (empirical (snap (S.X ω) t)) (β t (S.X ω)) |
            MeasurableSpace.comap (fun ω => snap (S.X ω) t) inferInstance]) ∧
        (S.P[fun ω => f t (snap (S.X ω) t i) (empirical (snap (S.X ω) t)) (β t (S.X ω)) |
            MeasurableSpace.comap (fun ω => snap (S.X ω) t) inferInstance]
          ≤ᵐ[S.P] fun ω => f t (snap (S.X ω) t i) (empirical (snap (S.X ω) t))
            (βt t (snap (S.X ω) t))) := by sorry

end ClosedLoopMFG.MarkovNash
