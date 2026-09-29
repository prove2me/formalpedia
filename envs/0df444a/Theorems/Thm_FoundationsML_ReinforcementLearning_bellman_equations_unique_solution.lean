-- Prove2me | Theorems.Thm_FoundationsML_ReinforcementLearning_bellman_equations_unique_solution
-- name    : FoundationsML.ReinforcementLearning.bellman_equations_unique_solution
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-20T04:38:29.51793+00:00
-- url     : https://prove2.me/theorems/81759717-d680-4349-80b7-c04eb5ef3b1f
-- title:
--   Theorem 17.10 — Unique solution of Bellman's equations (goal)
-- statement:
--   **Statement (Theorem 17.10, p. 386, PDF p. 403, eq. (17.7)).** For a finite MDP, Bellman's
--   equations admit a unique solution given by
--   $$V_\pi = (I-\gamma P)^{-1} R,$$
--   where $P$ is the transition-probability matrix induced by the fixed policy $\pi$
--   ($P_{s,s'}=P[s'\mid s,\pi(s)]$) and $R$ is its induced expected-reward vector
--   ($R_s=\mathbb E[r(s,\pi(s))]$). The book's proof shows $\lVert P\rVert_\infty = 1$ (from
--   $P$'s row-stochasticity), hence $\lVert\gamma P\rVert_\infty=\gamma<1$; the eigenvalues of
--   $\gamma P$ are therefore all of modulus less than one, so $1$ is not an eigenvalue of
--   $\gamma P$ and $I-\gamma P$ is invertible.
--
--   This is the mission's capstone: a finite-dimensional linear-algebra fact (matrix
--   invertibility via an operator-norm bound) that turns the fixed-point characterization of a
--   policy's value (Proposition 17.9) into a closed-form, computable expression — the value of
--   any fixed policy on a finite MDP can be obtained by inverting a single $|S|\times|S|$ matrix.
--
--   **Formalization Note.** `P` in `(I-\gamma P)` is the matrix induced by the *fixed* policy
--   $\pi$ (`InducedTransition`), not the raw MDP kernel indexed by an unfixed action. The
--   statement is a conjunction of three parts: (i) `IsUnit (1 - γ • P)`, the invertibility of
--   $I-\gamma P$ — genuine linear-algebra content, not unfolding, per the book's own
--   operator-norm argument; (ii) the actual policy value function `PolicyValue` equals the
--   closed-form solution `(1 - γ • P)⁻¹ *ᵥ R`; and (iii) uniqueness — any `V` satisfying the
--   Bellman equations (17.6) equals that same closed form.
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, p. 386, Theorem 17.10 (PDF p. 403)

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsPolicy
import Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel
import Definitions.Def_FoundationsML_ReinforcementLearning_PolicyValue
import Definitions.Def_FoundationsML_ReinforcementLearning_InducedTransition
import Definitions.Def_FoundationsML_ReinforcementLearning_InducedReward

open Matrix

namespace FoundationsML.ReinforcementLearning

/-- Theorem 17.10 (Mohri, Rostamizadeh & Talwalkar, *Foundations of Machine Learning*, 2nd ed.,
MIT Press 2018, p. 386, PDF p. 403). For a finite MDP, Bellman's equations admit a unique
solution given by `V_π = (I − γP)⁻¹R`, where `P` is the transition-probability matrix induced
by the fixed policy `π` (`P_{s,s'} = P[s'|s,π(s)]`) and `R` is its induced expected-reward
vector (`R_s = E[r(s,π(s))]`).

**Formalization Note.** `P` in `(I − γP)` is `Matrix.of (InducedTransition π P)`, the matrix
induced by the *fixed* policy `π` (not the raw MDP kernel indexed by an unfixed action), per
`BRIEF.md`'s pitfall note. The three conjuncts state: (i) `(I − γP)` is invertible — proved in
the book via the operator-norm bound `‖γP‖∞ = γ < 1`, genuine linear-algebra content, not
unfolding; (ii) the actual policy value `V_π` (`PolicyValue`) equals the closed-form solution
`(I−γP)⁻¹R`; and (iii) uniqueness — any `V` satisfying the Bellman equations (17.6) equals that
same closed form. -/
theorem bellman_equations_unique_solution {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    (π : S → A → ℝ) (hπ : IsPolicy π)
    (P : S → A → S → ℝ) (hP : IsTransitionKernel P)
    (Er : S → A → ℝ) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) :
    IsUnit (1 - γ • (Matrix.of (InducedTransition π P))) ∧
    (fun s => PolicyValue π P Er γ s) =
      (1 - γ • (Matrix.of (InducedTransition π P)))⁻¹ *ᵥ InducedReward π Er ∧
    ∀ V : S → ℝ,
      (∀ s : S, V s = InducedReward π Er s + γ * ∑ s' : S, InducedTransition π P s s' * V s') →
        V = (1 - γ • (Matrix.of (InducedTransition π P)))⁻¹ *ᵥ InducedReward π Er := by sorry

end FoundationsML.ReinforcementLearning
