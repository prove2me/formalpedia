-- Prove2me | Theorems.Thm_BinarySketchTruncation_Opposite_Supplement_proposition_3
-- name    : BinarySketchTruncation.Opposite.Supplement.proposition_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-15T18:06:16.416936+00:00
-- url     : https://prove2.me/theorems/186aa44b-d0e8-4960-9488-82fa8577675e
-- title:
--   Proposition 3 — addition under opposite monotonicity
-- statement:
--   Let k ≥ 0, and let P₀ and P₁ be arbitrary joint probability laws of binary vectors (U,V) ∈ 𝔽₂ᵏ × 𝔽₂ᵏ. For every fixed v, assume that P₀(u,v) is non-increasing in each coordinate of u and P₁(u,v) is non-decreasing in each coordinate of u. Then, as binary experiments,
--
--   $$
--   U\succeq U\oplus V.
--   $$
--
--   There is one row-stochastic kernel that transforms the law of U to the law of U ⊕ V simultaneously under both hypotheses. No independence, positive-mass or nondegeneracy assumption is imposed on the joint laws. The result is the experiment comparison used in evaluating unate functions.
--
--   Differences from the source:
--   - encoding: binary joint laws and coordinatewise opposite monotonicity → Bool-indexed PMFs on Fin-indexed ZMod 2 vectors, with adjacent-coordinate inequalities on real masses; reason: false denotes hypothesis 0, true denotes 1, and adjacent inequalities express exactly the order on the binary cube; PMF masses are finite
-- source:
--   Robinson D.H. Cung, Adway Girish, Emre Telatar, STOC 2027 submission #341 (October 2026), p. 9 (PDF p. 10), Proposition 3

import Mathlib
import Definitions.Def_BinarySketchTruncation_Opposite_Model

namespace BinarySketchTruncation.Opposite.Supplement

/-- Proposition 3, printed p. 9 (PDF 10). No independence or positive-mass
assumption: the two joint laws are arbitrary apart from opposite monotonicity. -/
theorem proposition_3 {k : ℕ} (P : Experiment (Vec k × Vec k))
    (h₀ : ∀ (v u : Vec k) (i : Fin k),
      (P false (Function.update u i 1, v)).toReal ≤
        (P false (Function.update u i 0, v)).toReal)
    (h₁ : ∀ (v u : Vec k) (i : Fin k),
      (P true (Function.update u i 0, v)).toReal ≤
        (P true (Function.update u i 1, v)).toReal) :
    Dominates (fun h => (P h).map Prod.fst)
      (fun h => (P h).map (fun uv => uv.1 + uv.2)) := by sorry

end BinarySketchTruncation.Opposite.Supplement
