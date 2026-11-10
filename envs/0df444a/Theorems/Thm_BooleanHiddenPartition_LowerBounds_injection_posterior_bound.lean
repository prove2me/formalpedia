-- Prove2me | Theorems.Thm_BooleanHiddenPartition_LowerBounds_injection_posterior_bound
-- name    : BooleanHiddenPartition.LowerBounds.injection_posterior_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T15:23:00.902132+00:00
-- url     : https://prove2.me/theorems/4ae144fe-a179-45dc-a85d-a7410a28e7c5
-- title:
--   Lemma 9 — Weighted random-injection posterior bound
-- statement:
--   For each k there is K>0 depending only on k. For all integers t≥k≥d≥0, Boolean f, probability masses q with zero correlations below degree d, and nu:{±1}^t→[0,1], let Q=E_uniform nu and C=−log_2 Q. Choose an ordered injection pi:[k]→[t] uniformly. Let N(pi)=E_uniform[q(x_pi)nu(x)], and let p_pi be its normalized posterior, zero when N=0. Then for Q>0 and d>0,
--
--   $$\mathbb E_\pi[N(\pi)(\mathbb E_{p_\pi}f(x_\pi))^2]\leq KQ((C+1)/t)^d.$$
--
--   For Q=0 the left side equals zero; for Q>0 and d=0 it is at most Q. The constant precedes f,q,nu,t,d and pi. This retains the vanishing-mass cases and the zero-dimensional case used in the proof.
--
--   Differences from the source:
--   - encoding: Coordinates in {+1,−1} indexed from 1 → Fin-indexed Bool coordinates with true=−1, and explicit finite averages; reason: The sign map is a bijection and preserves ordered blocks, parities, distributions and all source instances.
--   - encoding: An O-bound with the dependencies specified in the text → A positive existential constant before every varying datum; reason: This spells out the source uniformity without choosing a numeral or weakening a power.
--   - encoding: The proof separately treats Q=0 and d=0 as trivial (p.19) → An explicit zero left side for Q=0 and the bound by Q for d=0; reason: N≤Q and the posterior bias has absolute value at most one, giving these exact branches even at t=k=d=0 without a division by t.
--   - reading: C=−log Q with the base-two convention of Lemma 4 → logCost Q on the positive-Q branch; reason: This uses the same logarithm as the source estimate.
-- source:
--   Mark Bun, Joao F. Doriguello, John Kallaugher, Nadezhda Voronova, STOC 2027 submission #1085 (October 2026), p. 18, Lemma 9.

import Definitions.Def_BooleanHiddenPartition_LowerBounds_Posteriors

open scoped BigOperators ENNReal
open Classical
set_option autoImplicit false

namespace BooleanHiddenPartition.LowerBounds

noncomputable section

/-- Lemma 9, p.18. Its proof on p.19 treats Q=0 and d=0 separately. -/
theorem injection_posterior_bound (k : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (t d : ℕ), k ≤ t → d ≤ k →
      ∀ (f : Cube k → Bool) (q : Cube k → ℝ) (ν : Cube t → ℝ),
      IsMass q → moments f q d → (∀ x, 0 ≤ ν x ∧ ν x ≤ 1) →
      (if cubeMean ν = 0 then injectionBias f q ν = 0
       else if d = 0 then injectionBias f q ν ≤ cubeMean ν
       else injectionBias f q ν ≤
         K * cubeMean ν * ((logCost (cubeMean ν) + 1) / t) ^ d) := by sorry

end

end BooleanHiddenPartition.LowerBounds
