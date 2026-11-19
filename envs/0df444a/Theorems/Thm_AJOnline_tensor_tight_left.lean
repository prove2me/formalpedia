-- Prove2me | Theorems.Thm_AJOnline_tensor_tight_left
-- name    : AJOnline.tensor_tight_left
-- status  : Proved
-- author  : @martelus trismortuus
-- created : 2026-11-18T15:35:34.560203+00:00
-- url     : https://prove2.me/theorems/008f7b9e-b94a-4617-96c2-c855ba1b10f2
-- title:
--   The tensor cannot beat its components
-- statement:
--   Let $C,D$ be costed games, $\sigma$ a strategy on $C$ and $\tau$ a strategy on $D$, and suppose $\mathrm{opt}_D$ of the empty play is $0$. If $\sigma\otimes\tau$ is $(\rho,b)$-competitive on $C\otimes D$, then $\sigma$ is $(\rho,b)$-competitive on $C$.
--
--   So the ratio $\max(\rho_1,\rho_2)$ in the tensor law cannot be improved in general.
-- source:
--   New statement introduced by this mission (no prior source); complement to AJOnline.tensor_competitive

import Mathlib
import Definitions.Def_AJOnline_CostedGame

namespace AJOnline

open AJGames
open scoped ENNReal NNReal

universe u

/-- **Tightness of the tensor bound.** If `σ ⊗ τ` is `(ρ, b)`-competitive on `C ⊗ D` and `D`'s
offline optimum on the empty play is `0`, then `σ` alone is `(ρ, b)`-competitive on `C`: Opponent may
keep every request in the left component. Hence no ratio below `ρ₁` (and, symmetrically, `ρ₂`) works for
the tensor, so `max ρ₁ ρ₂` in `tensor_competitive` is optimal. AJ axioms used: G3 for `C` (the
left-only play satisfies the tensor's alternation), G1 for `D`; no switching occurs, so T2 is not used. -/
theorem tensor_tight_left (C D : CostedGame.{u}) (σ : Strategy C.G) (τ : Strategy D.G) (ρ b : ℝ≥0)
    (hD : D.opt [] = 0) (h : Competitive (C.tensor D) (tensorS σ τ) ρ b) :
    Competitive C σ ρ b := by sorry

end AJOnline
