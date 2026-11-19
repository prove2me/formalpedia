-- Prove2me | Theorems.Thm_AJOnline_tensor_competitive
-- name    : AJOnline.tensor_competitive
-- status  : Proved
-- author  : @martelus trismortuus
-- created : 2026-11-18T15:34:37.805146+00:00
-- url     : https://prove2.me/theorems/ac941b6f-4f28-477a-b3fe-88d6853c6087
-- title:
--   Competitive ratios across the tensor: $\max(\rho_1,\rho_2)$
-- statement:
--   Let $C$ and $D$ be costed games. Let $\sigma$ be $(\rho_1,b_1)$-competitive on $C$ and $\tau$ be $(\rho_2,b_2)$-competitive on $D$. Then $\sigma\otimes\tau$ is
--   $$(\max(\rho_1,\rho_2),\ b_1+b_2)\text{-competitive on } C\otimes D,$$
--   where Opponent interleaves the two request streams freely.
--
--   This is a composition law for competitive ratios. The tensor of strategies is well defined only because only Opponent switches component.
-- source:
--   New statement introduced by this mission (no prior source); games and tensor of strategies from S. Abramsky, R. Jagadeesan, Games and full completeness for multiplicative linear logic, J. Symbolic Logic 59(2) (1994) 543-574, https://arxiv.org/abs/1311.6057; competitiveness from A. Borodin, R. El-Yaniv, Online Computation and Competitive Analysis, CUP 1998, Definition 1.1

import Mathlib
import Definitions.Def_AJOnline_CostedGame

namespace AJOnline

open AJGames
open scoped ENNReal NNReal

universe u

/-- **Competitive ratios across the tensor.** If `σ` is `(ρ₁, β₁)`-competitive on the online problem
`C` and `τ` is `(ρ₂, β₂)`-competitive on `D`, then playing them side by side, `σ ⊗ τ`, is
`(max ρ₁ ρ₂, β₁ + β₂)`-competitive on `C ⊗ D`, where Opponent interleaves the two request streams.
AJ axioms used: T2 (only Opponent switches component), through the fact that `σ ⊗ τ` is a strategy
(`tensorS`, determinism); the inequality itself uses only the definition of `σ ⊗ τ`. -/
theorem tensor_competitive (C D : CostedGame.{u}) (σ : Strategy C.G) (τ : Strategy D.G)
    (ρ₁ β₁ ρ₂ β₂ : ℝ≥0) (hσ : Competitive C σ ρ₁ β₁) (hτ : Competitive D τ ρ₂ β₂) :
    Competitive (C.tensor D) (tensorS σ τ) (max ρ₁ ρ₂) (β₁ + β₂) := by sorry

end AJOnline
