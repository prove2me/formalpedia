-- Prove2me | Theorems.Thm_BarelyTestable_LowerBound_soundness
-- name    : BarelyTestable.LowerBound.soundness
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T12:22:16.313323+00:00
-- url     : https://prove2.me/theorems/857612e6-87ef-4428-bc38-5161abb81eff
-- title:
--   Proposition 3.4 — simultaneous distance from every submodular repair
-- statement:
--   For all sufficiently large $m$, a function from the NO law satisfies
--
--   $$\Pr\!\left[\operatorname{dist}(F^{(-1)},\mathrm{Submodular})\ge10^{-8}\right]\ge8/10.$$
--
--   The event means that the same sampled function requires changing at least a $10^{-8}$ fraction of its values for every real submodular repair simultaneously. The threshold depends on none of the sampled data or repairs.
--
--   Differences from the source:
--   - encoding: two action bits and two halves with m blocks of m coordinates → Coord m = Bool ⊕ ((Fin m × Fin m) ⊕ (Fin m × Fin m)); reason: this coordinate type has 2m²+2 elements and coordEquiv explicitly renames it to Fin (2m²+2)
--   - encoding: independent uniform labels and table entries → uniform counting probability on the full finite product Sample m; reason: every assignment occurs once, giving exactly the independent product law and its pushforward to the constructed real functions
--   - encoding: distance at least 10⁻⁸ to the submodular property → the universal Far predicate over every real submodular repair; reason: on a finite cube the attainable mismatch counts form a nonempty finite subset of the natural numbers, so the minimum is attained and the two conditions coincide
--   - encoding: F^(−1) → hard r false; reason: the Boolean false selects σ = −1 (NO)
-- source:
--   Diptaksho Palit, Yuichi Yoshida, STOC 2027 submission #722 (October 2026), Proposition 3.4, p. 13 (printed = PDF page); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/722.pdf; PDF SHA256 a095e6ef801edf5b0ce3967efca977e04b7a0b4374e874116509d73837bd14f3

import Mathlib
import Definitions.Def_BarelyTestable_LowerBound_Construction

set_option autoImplicit false

namespace BarelyTestable.LowerBound

open NonmonotoneSubmod.Shared MeasureTheory

/-- Proposition 3.4, p.13: one sampled function is far from every real submodular repair. -/
theorem soundness :
    ∃ M : ℕ, ∀ m : ℕ, M ≤ m →
      (8/10 : ℝ) ≤ uniformProb (fun r : Sample m =>
        Far Submodular (1/10^8 : ℝ) (hard r false)) := by sorry

end BarelyTestable.LowerBound
