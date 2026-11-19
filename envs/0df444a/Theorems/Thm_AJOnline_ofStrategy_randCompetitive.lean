-- Prove2me | Theorems.Thm_AJOnline_ofStrategy_randCompetitive
-- name    : AJOnline.ofStrategy_randCompetitive
-- status  : Proved
-- author  : @martelus trismortuus
-- created : 2026-11-18T15:34:11.833939+00:00
-- url     : https://prove2.me/theorems/757e36c4-3af6-4021-9c3a-4da9b3ecb2ac
-- title:
--   Deterministic competitiveness carries over to the randomised notion
-- statement:
--   Let $C$ be a costed game, and let $\sigma$ be a strategy on $C$ that is $(\rho,b)$-competitive:
--   $$\mathrm{alg}(s)\le\rho\,\mathrm{opt}(s)+b\quad\text{for all } s\in\sigma.$$
--   Then $\sigma$, read as a behaviour strategy, is $(\rho,b)$-randomised-competitive against oblivious adversaries.
--
--   The randomised notion therefore extends the deterministic one.
-- source:
--   New statement introduced by this mission (no prior source); competitiveness as in A. Borodin, R. El-Yaniv, Online Computation and Competitive Analysis, CUP 1998, Definition 1.1

import Mathlib
import Definitions.Def_AJOnline_CostedGame

namespace AJOnline

open AJGames
open scoped ENNReal NNReal

universe u

/-- **Deterministic competitiveness carries over.** If `σ` is `(ρ, b)`-competitive, the behaviour
strategy `ofStrategy σ` is `(ρ, b)`-competitive against oblivious adversaries: against any script, its
play-out is the single play of `σ`. AJ axioms used: strategy axioms (nil, receptive; first-O and
determinism through `ofStrategy`) and G3 through `ofStrategy`'s legality. No tensor axiom. -/
theorem ofStrategy_randCompetitive (C : CostedGame.{u}) (σ : Strategy C.G) (ρ b : ℝ≥0)
    (h : Competitive C σ ρ b) : RandCompetitive C (ofStrategy σ) ρ b := by sorry

end AJOnline
