-- Prove2me | Theorems.Thm_BarelyTestable_LowerBound_balanced_centers
-- name    : BarelyTestable.LowerBound.balanced_centers
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T12:23:10.203222+00:00
-- url     : https://prove2.me/theorems/ce97bed8-5df2-497b-8650-8362b3419fd9
-- title:
--   Lemma 3.9 — balanced-center concentration
-- statement:
--   For all sufficiently large $m$, under the independent uniform law of the two entire label maps,
--
--   $$\Pr\!\left[|C'|\le\tfrac14\,2^{-2m}2^{2m^2}\right]\le\tfrac1{10}.$$
--
--   Here $C'$ consists exactly of centers balanced in both halves. The bad event includes equality, and the eventual threshold is uniform over all later choices of repairs and algorithms.
--
--   Differences from the source:
--   - encoding: independent random maps and sufficiently large m → uniform counting law on LabelMap m × LabelMap m, with ∃ M ∀ m ≥ M; reason: this is exactly the product sampling law; a negative exponent is written as (1/2)^(2m) to avoid natural truncation
-- source:
--   Diptaksho Palit, Yuichi Yoshida, STOC 2027 submission #722 (October 2026), Lemma 3.9, p. 16 (printed = PDF page); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/722.pdf; PDF SHA256 a095e6ef801edf5b0ce3967efca977e04b7a0b4374e874116509d73837bd14f3

import Mathlib
import Definitions.Def_BarelyTestable_LowerBound_Loads

set_option autoImplicit false

namespace BarelyTestable.LowerBound

open NonmonotoneSubmod.Shared MeasureTheory

/-- Lemma 3.9, p.16: the bad event includes equality. -/
theorem balanced_centers :
    ∃ M : ℕ, ∀ m : ℕ, M ≤ m →
      uniformProb (fun r : LabelMap m × LabelMap m =>
        (balancedCenters r.1 r.2 : ℝ) ≤ (1/4 : ℝ) * (1/2 : ℝ)^(2*m) * 2^(2*m^2)) ≤
      (1/10 : ℝ) := by sorry

end BarelyTestable.LowerBound
