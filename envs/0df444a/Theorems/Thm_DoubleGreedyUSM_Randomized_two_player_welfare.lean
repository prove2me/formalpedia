-- Prove2me | Theorems.Thm_DoubleGreedyUSM_Randomized_two_player_welfare
-- name    : DoubleGreedyUSM.Randomized.two_player_welfare
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T01:10:41.259992+00:00
-- url     : https://prove2.me/theorems/55c71ece-c2f8-46f4-83b8-9596a7cec083
-- title:
--   Theorem I.4 — three-quarter approximation for two-player submodular welfare
-- statement:
--   Let two players value subsets of a finite ground set by nonnegative, normalized, monotone submodular functions $f_1$ and $f_2$. An allocation is determined by the first player's set $S$; the second receives $\mathcal N\setminus S$. Put $g(S)=f_1(S)+f_2(\mathcal N\setminus S)$ and run Algorithm 2 on $g$ in any order. Then
--
--   $$3\max_{S\subseteq\mathcal N}g(S)\le4\,\mathbb E[g(X_n)].$$
--
--   The maximum on the left is exactly the optimum welfare over two-player partitions.
--
--   **Formalization Note** This is Proof (2) of Theorem I.4, which applies Algorithm 2 to $g$. The statement does not encode its two-oracle-query implementation or running time.
-- source:
--   Buchbinder, Feldman, Naor, Schwartz, A Tight Linear Time (1/2)-Approximation for Unconstrained Submodular Maximization, FOCS 2012 version, Theorem I.4 (PDF p. 2), §IV preamble (PDF p. 6), Proof (2) (PDF p. 7)

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_NonmonotoneSubmod_Shared_OPT
import Definitions.Def_DoubleGreedyUSM_Randomized_Algorithm2

namespace DoubleGreedyUSM.Randomized

/-- Theorem I.4, Proof (2) (PDF pp. 2, 7): Algorithm 2 on the two-player welfare
objective is a three-quarter approximation. -/
theorem two_player_welfare {X : Type} [Fintype X] [DecidableEq X]
    (f₁ f₂ : Finset X → ℝ)
    (hsub₁ : NonmonotoneSubmod.Shared.Submodular f₁)
    (hsub₂ : NonmonotoneSubmod.Shared.Submodular f₂)
    (hmono₁ : ∀ A B : Finset X, A ⊆ B → f₁ A ≤ f₁ B)
    (hmono₂ : ∀ A B : Finset X, A ⊆ B → f₂ A ≤ f₂ B)
    (hnonneg₁ : ∀ S : Finset X, 0 ≤ f₁ S)
    (hnonneg₂ : ∀ S : Finset X, 0 ≤ f₂ S)
    (hnorm₁ : f₁ ∅ = 0) (hnorm₂ : f₂ ∅ = 0)
    (l : List X) (hl : l.Nodup) (hcov : ∀ x : X, x ∈ l) :
    let g : Finset X → ℝ := fun S => f₁ S + f₂ Sᶜ
    3 * NonmonotoneSubmod.Shared.OPT g ≤
      4 * expect (state g l l.length) (fun s => g s.1) := by sorry

end DoubleGreedyUSM.Randomized
