-- Prove2me | Theorems.Thm_BarelyTestable_LowerBound_balanced_pairs
-- name    : BarelyTestable.LowerBound.balanced_pairs
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T12:23:04.930346+00:00
-- url     : https://prove2.me/theorems/a0184e41-f1da-47a5-8f75-496a914b94cb
-- title:
--   Claim 3.18 — many balanced control pairs
-- statement:
--   There exists a threshold $M$ such that for every $m\ge M$,
--
--   $$\#\{(X,Y):X,Y\text{ are balanced}\}\ge2^{2m^2}/2.$$
--
--   Balance uses the exact inclusive real endpoints $m/4+1$ and $3m/4-1$ in every block. The threshold is independent of any labels, table or algorithm.
--
--   Differences from the source:
--   - encoding: for large enough m → there exists M before the universally quantified m; reason: explicit eventual quantification of the source threshold; the count ranges over all ordered pairs of half-subsets
-- source:
--   Diptaksho Palit, Yuichi Yoshida, STOC 2027 submission #722 (October 2026), Claim 3.18, p. 24 (printed = PDF page); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/722.pdf; PDF SHA256 a095e6ef801edf5b0ce3967efca977e04b7a0b4374e874116509d73837bd14f3

import Mathlib
import Definitions.Def_BarelyTestable_LowerBound_Loads

set_option autoImplicit false

namespace BarelyTestable.LowerBound

open NonmonotoneSubmod.Shared MeasureTheory

/-- Claim 3.18, p.24; the threshold is independent of a pair or any sampled labels. -/
theorem balanced_pairs :
    ∃ M : ℕ, ∀ m : ℕ, M ≤ m → (2 : ℝ)^(2*m^2) / 2 ≤ balancedPairs m := by sorry

end BarelyTestable.LowerBound
