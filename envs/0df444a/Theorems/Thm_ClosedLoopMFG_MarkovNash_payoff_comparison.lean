-- Prove2me | Theorems.Thm_ClosedLoopMFG_MarkovNash_payoff_comparison
-- name    : ClosedLoopMFG.MarkovNash.payoff_comparison
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T03:32:34.515747+00:00
-- url     : https://prove2.me/theorems/7a92e3fd-a180-4754-9cd3-4ccbef186ee2
-- title:
--   Proof of Proposition 2.2 — the Markovian selection does at least as well: $J^n_i(\beta,\alpha^{-i})\le J^n_i(\widetilde\beta,\alpha^{-i})$
-- statement:
--   Assume Assumption A. Fix a player $i$, Markovian controls $\alpha^j$ for $j\ne i$, and an admissible closed-loop control $\beta$ for player $i$. Let $\boldsymbol Y$ be a solution of the state system of the profile $(\beta,\alpha^{-i})$ (player $i$ uses $\beta$, every $j\ne i$ uses $\alpha^j$), with empirical measures $\nu^n_t$, and let $\widetilde\beta:[0,T]\times(\mathbb R^d)^n\to A$ be a Borel function satisfying (4.6) and (4.7) along $\boldsymbol Y$ for each $t\in[0,T]$. Then
--   $$J^n_i(\beta,\alpha^{-i})\le J^n_i(\widetilde\beta,\alpha^{-i}),$$
--   where the left side is computed on $\boldsymbol Y$ and the right side on any solution of the state system of the Markovian profile $(\widetilde\beta,\alpha^{-i})$.
--
--   This is the comparison step of the paper's proof: by Markovian projection (Theorem 2.14) the system driven by $\widetilde\beta$ has the same time marginals as $\boldsymbol Y$, and (4.7) then gives the inequality of payoffs. Combined with the Markovian $\epsilon$-Nash property it yields Proposition 2.2.
--
--   **Formalization Note** The paper writes this for player 1; it is stated for an arbitrary player $i$. The final step of the printed chain, $J^n_1(\widetilde\beta,\alpha^2,\dots,\alpha^n)\le J^n_1(\alpha^1,\dots,\alpha^n)+\epsilon$, is the Markovian Nash hypothesis and is not part of this statement. Payoffs are computed on given weak solutions; the inequality is asserted for the given solution $\boldsymbol Y$ of the closed-loop profile (along which (4.6)–(4.7) hold) and every solution of the Markovian profile, matching the paper's use of "the unique solution" $\widetilde{\boldsymbol Y}$ and uniqueness in law. Assumption B is not needed once $\widetilde\beta$ is given.
-- source:
--   Lacker, On the convergence of closed-loop Nash equilibria to the mean field game limit, arXiv:1808.02745v1, p. 21, proof of Proposition 2.2 (Section 4.3)

import Mathlib
import Definitions.Def_ClosedLoopMFG_MarkovNash_Model
import Definitions.Def_ClosedLoopMFG_MarkovNash_Game

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace ClosedLoopMFG.MarkovNash

/-- Lacker, arXiv:1808.02745v1, proof of Proposition 2.2 (§4.3, p. 21): the payoff comparison.
Let player `i` use an admissible closed-loop control `β` and every other player `j` a Markovian
control `α̃^j`, and let `Y` be a solution of that state system (empirical measure `ν^n`). If a
Borel `A`-valued `β̃ : [0, T] × (ℝ^d)^n → A` satisfies (4.6) and (4.7) along `Y` for each
`t ∈ [0, T]`, then `J^n_i(β, α̃^{-i}) ≤ J^n_i(β̃, α̃^{-i})`, for every solution of the state system
of the Markovian profile `(β̃, α̃^{-i})`. -/
theorem payoff_comparison {n d : ℕ} [NeZero n] {T : ℝ≥0} (hT : 0 < T)
    {EA : Type*} [NormedAddCommGroup EA] [NormedSpace ℝ EA] [MeasurableSpace EA] [BorelSpace EA]
    (A : Set EA) (lam : PR d) (b : ℝ → E d → PR d → EA → E d)
    (f : ℝ → E d → PR d → EA → ℝ) (g : E d → PR d → ℝ)
    (hA : AssumptionA T A b f g)
    (α : Fin n → ℝ → (Fin n → E d) → EA) (i : Fin n)
    (hα : ∀ j, j ≠ i → IsMarkovControl (T := T) A (α j))
    (β : ℝ → (Fin n → Path d T) → EA) (hβ : IsAdmissible A β)
    (S : NSol n d T lam (drift b (Function.update (fun j => liftM (α j)) i β)))
    (βt : ℝ → (Fin n → E d) → EA) (hβt : IsMarkovControl (T := T) A βt)
    (h46 : ∀ t ∈ Set.Icc (0 : ℝ) T,
      (fun ω => b t (snap (S.X ω) t i) (empirical (snap (S.X ω) t)) (βt t (snap (S.X ω) t)))
        =ᵐ[S.P] S.P[fun ω => b t (snap (S.X ω) t i) (empirical (snap (S.X ω) t)) (β t (S.X ω)) |
          MeasurableSpace.comap (fun ω => snap (S.X ω) t) inferInstance])
    (h47 : ∀ t ∈ Set.Icc (0 : ℝ) T,
      S.P[fun ω => f t (snap (S.X ω) t i) (empirical (snap (S.X ω) t)) (β t (S.X ω)) |
          MeasurableSpace.comap (fun ω => snap (S.X ω) t) inferInstance]
        ≤ᵐ[S.P] fun ω => f t (snap (S.X ω) t i) (empirical (snap (S.X ω) t))
          (βt t (snap (S.X ω) t)))
    (S' : NSol n d T lam (drift b (fun j => liftM (Function.update α i βt j)))) :
    Jn b f g (Function.update (fun j => liftM (α j)) i β) S i ≤
      Jn b f g (fun j => liftM (Function.update α i βt j)) S' i := by sorry

end ClosedLoopMFG.MarkovNash
