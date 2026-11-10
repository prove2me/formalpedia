-- Prove2me | Theorems.Thm_BooleanHiddenPartition_LowerBounds_fourier_level_bound
-- name    : BooleanHiddenPartition.LowerBounds.fourier_level_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T15:20:56.423961+00:00
-- url     : https://prove2.me/theorems/9dd1edab-9242-4c8d-a79d-a59d908feb28
-- title:
--   Lemma 4 — Bounded scalar Fourier level mass
-- statement:
--   Let t be positive and let nu:{±1}^t→[0,1] have uniform mean Q>0. Put C=−log_2 Q. For every positive integer r≤C,
--
--   $$Q^{-2}\sum_{|U|=r}\widehat\nu(U)^2\leq(4C/r)^r.$$
--
--   The numeral 4 and the range r≤C are exact. Fourier coefficients use uniform expectation; this level estimate is the scalar analytic input to the injection lemma.
--
--   Differences from the source:
--   - encoding: Coordinates in {+1,−1} indexed from 1 → Fin-indexed Bool coordinates with true=−1, and explicit finite averages; reason: The sign map is a bijection and preserves ordered blocks, parities, distributions and all source instances.
--   - reading: C=−log Q, with the proof using Q=2^(−C) → C=−Real.log(Q)/Real.log(2); reason: The calculation on p.13 fixes base two; positivity of Q excludes logarithm and inverse junk.
-- source:
--   Mark Bun, Joao F. Doriguello, John Kallaugher, Nadezhda Voronova, STOC 2027 submission #1085 (October 2026), p. 13, Lemma 4.

import Definitions.Def_BooleanHiddenPartition_LowerBounds_Scalar

open scoped BigOperators ENNReal
open Classical
set_option autoImplicit false

namespace BooleanHiddenPartition.LowerBounds

noncomputable section

/-- Lemma 4, p.13. Logarithms are base 2, as in its proof. -/
theorem fourier_level_bound {t : ℕ} (ht : 0 < t) (ν : Cube t → ℝ)
    (hν : ∀ x, 0 ≤ ν x ∧ ν x ≤ 1) (hQ : 0 < cubeMean ν)
    (r : ℕ) (hr : 0 < r) (hrC : (r : ℝ) ≤ logCost (cubeMean ν)) :
    (cubeMean ν)⁻¹ ^ 2 *
      (∑ U : Finset (Fin t), if U.card = r then fourier ν U ^ 2 else 0) ≤
        (4 * logCost (cubeMean ν) / r) ^ r := by sorry

end

end BooleanHiddenPartition.LowerBounds
