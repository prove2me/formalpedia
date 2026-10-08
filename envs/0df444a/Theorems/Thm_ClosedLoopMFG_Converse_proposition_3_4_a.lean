-- Prove2me | Theorems.Thm_ClosedLoopMFG_Converse_proposition_3_4_a
-- name    : ClosedLoopMFG.Converse.proposition_3_4_a
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T04:29:02.77999+00:00
-- url     : https://prove2.me/theorems/2d830358-b530-4ae4-a2ea-f8814842e4cd
-- title:
--   Proposition 3.4(a) — a relaxed Markovian $\epsilon$-Nash equilibrium yields a strict one with the same state law
-- statement:
--   Suppose Assumptions A and B hold, let $n\ge1$ and $\epsilon\ge0$. Let $\Lambda=(\Lambda^1,\dots,\Lambda^n)$ be a relaxed Markovian $\epsilon$-Nash equilibrium of the $n$-player game. Then there exists a Markovian $\epsilon$-Nash equilibrium $\alpha=(\alpha^1,\dots,\alpha^n)$ whose state system has a solution, and
--   $$X[\Lambda]\ \overset{d}{=}\ X[\alpha],$$
--   i.e. the state vectors of the two systems have the same law on $(\mathcal C^d)^n$.
--
--   Under convexity, relaxed equilibria can be purified without changing the law of the states. This is how Theorem 2.11 is deduced from its relaxed version, Theorem 3.10.
--
--   **Formalization Note** The paper's Proposition 3.4 has a second part (b), the closed-loop analogue, which is not posed. The equality in law is asserted for every solution of either system; the solution of $\alpha$'s system is asserted to exist, so that $\alpha$ is not an equilibrium vacuously.
-- source:
--   Lacker, On the convergence of closed-loop Nash equilibria to the mean field game limit, arXiv:1808.02745v1, p. 15, Proposition 3.4(a)

import Mathlib
import Definitions.Def_ClosedLoopMFG_Converse_Model
import Definitions.Def_ClosedLoopMFG_Converse_Game
import Definitions.Def_ClosedLoopMFG_Converse_Equilibrium

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace ClosedLoopMFG.Converse

theorem proposition_3_4_a {d : ℕ} {T : ℝ≥0} (hT : 0 < T) {EA : Type}
    [NormedAddCommGroup EA] [NormedSpace ℝ EA] [MeasurableSpace EA] [BorelSpace EA]
    (A : Set EA) (lam : PR d) (b : ℝ → ClosedLoopMFG.Limit.E d → PR d → EA → ClosedLoopMFG.Limit.E d) (f : ℝ → ClosedLoopMFG.Limit.E d → PR d → EA → ℝ)
    (g : ClosedLoopMFG.Limit.E d → PR d → ℝ)
    (hA : AssumptionA T A b f g) (hB : AssumptionB T A b f)
    {n : ℕ} [NeZero n] (ε : ℝ) (hε : 0 ≤ ε)
    (Λ : Fin n → ℝ → (Fin n → ClosedLoopMFG.Limit.E d) → PA A) (hΛ : IsRelaxedMarkovNash T A lam b f g ε Λ) :
    ∃ α : Fin n → ℝ → (Fin n → ClosedLoopMFG.Limit.E d) → EA,
      IsMarkovNash T A lam b f g ε α ∧
      Nonempty (NSol n d T lam (driftM T b α)) ∧
      ∀ (S : NSol n d T lam (driftR T b Λ)) (S' : NSol n d T lam (driftM T b α)),
        S.lawX = S'.lawX := by sorry

end ClosedLoopMFG.Converse
