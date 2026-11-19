-- Prove2me | Theorems.Thm_AJOnline_rand_tensor_competitive
-- name    : AJOnline.rand_tensor_competitive
-- status  : Open
-- author  : @martelus trismortuus
-- created : 2026-11-18T15:39:18.802704+00:00
-- url     : https://prove2.me/theorems/48a5cc11-cb76-4c60-958a-7bf35927a602
-- title:
--   Randomised tensor of competitive behaviour strategies
-- statement:
--   Let $C,D$ be costed games whose underlying games are open to Opponent. Let $\beta_A$ on $C$ and $\beta_B$ on $D$ be never-stopping behaviour strategies, $(\rho_1,b_1)$- and $(\rho_2,b_2)$-randomised-competitive respectively. Then $\beta_A\otimes\beta_B$ is
--   $$(\max(\rho_1,\rho_2),\ b_1+b_2)\text{-randomised-competitive on } C\otimes D .$$
--
--   This is the randomised counterpart of the deterministic tensor law.
-- source:
--   New statement introduced by this mission (no prior source); randomised counterpart of AJOnline.tensor_competitive

import Mathlib
import Definitions.Def_AJOnline_CostedGame
import Definitions.Def_AJGames_BehTensor

namespace AJOnline

open AJGames
open scoped ENNReal NNReal

universe u

/-- **Randomised tensor.** If the behaviour strategies `βA` and `βB` never stop, are `(ρ₁, b₁)`- and
`(ρ₂, b₂)`-competitive against oblivious adversaries, and Opponent may always move in both games,
then `βA ⊗ βB` is `(max ρ₁ ρ₂, b₁ + b₂)`-competitive on `C ⊗ D`. -/
theorem rand_tensor_competitive (C D : CostedGame.{u}) (βA : BehStrategy C.G) (βB : BehStrategy D.G)
    (ρ₁ b₁ ρ₂ b₂ : ℝ≥0) (hA : RandCompetitive C βA ρ₁ b₁) (hB : RandCompetitive D βB ρ₂ b₂)
    (hsA : βA.NonStop) (hsB : βB.NonStop) (hoA : OpenToOpponent C.G) (hoB : OpenToOpponent D.G) :
    RandCompetitive (C.tensor D) (tensorB βA βB) (max ρ₁ ρ₂) (b₁ + b₂) := by sorry

end AJOnline
